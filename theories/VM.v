From Coq Require Import
  List
  ZArith
  SetoidClass
  SetoidDec.
Import ListNotations.

From SLOT Require
  Setoids
  TransitionSystem
  Pid
  ListSelector
  IOHandler
  Mailbox.

Import Setoids TransitionSystem ListSelector Mailbox.
Export Pid IOHandler.

From Hammer Require Import
  Tactics.

From RecordUpdate Require Import
  RecordUpdate.

Open Scope positive_scope.

Section VM.
  Context `{IOH : IOHandler} {AppMessage : Type}.

  Let World := @h_state _ _ IOH.

  CoInductive Program (Mailbox : Set) : Type :=
  | p_dead : (* Program terminted *)
      Program Mailbox
  | p_yield :
      (* Interrupt the computation without producing any side effects.
      This primitive is used to softly introduce the concept of
      Erlang's "reductions", and to side-step termination checker,
      making programs non-Turing in a practically useful, as opposed
      to forced, way.

      In Erlang, reduction counting improves responsiveness of the
      system, in SLOT it *additionally* gives a structural argument
      "for free". *)
    forall {CTX : Type}
      (ctx : CTX)
      (continuation : CTX -> Program Mailbox),
    Program Mailbox
  | p_cont : (* Program is doing I/O *)
    forall (pending_req : Request)
      (continuation : Reply pending_req -> Program Mailbox),
      Program Mailbox
  | p_spawn : (* Spawn a new process: *)
    forall {Mailbox' : Set}
      (child : @Program Mailbox')
      (continuation : @Address Mailbox' -> Program Mailbox),
      Program Mailbox.

  Record Process :=
    { proc_mb_t : Set;
      proc_prog : @Program proc_mb_t;
    }.

  Record VM :=
    mkVM
      { (* State of the I/O handler *)
        world : World;
        (* Set of runnable processes *)
        runq : list (PID * Process);
        (* Set of sleeping processes *)
        sleepq : list (PID * Process);
        (* Counter that gets incremented when process spawns a child.
        This counter is used as a suffix of the child's pid *)
        child_ctr : Pid.FMap.t positive;
      }.

  #[export] Instance etaX : Settable _ := settable! mkVM <world; runq; sleepq; child_ctr>.

  Program Definition vm_setoid : Setoid VM :=
    {| equiv a b :=
        let (w1, rq1, sq1, cc1) := a in
        let (w2, rq2, sq2, cc2) := b in
        let w_eq := @equiv _ h_setoid in
        let p_eq := @equiv _ (setoid_permutation _) in
        w_eq w1 w2 /\
          p_eq rq1 rq2 /\
          p_eq sq1 sq2 /\
          @equiv _ (eq_setoid _) cc1 cc2;
    |}.
  Next Obligation.
    sauto unfold:Reflexive,Symmetric,Transitive
          use:Permutation_sym,Permutation_trans.
  Qed.

  Definition new_child_id (parent : PID) (v : VM) : VM * positive :=
    let cc := child_ctr v in
    let (cc, ctr) :=
      match Pid.FMap.find parent cc with
      | Some ctr =>
          (Pid.FMap.add parent (ctr + 1) cc, ctr)
      | None =>
          (Pid.FMap.add parent 2 cc, 1)
      end in
    (v<| child_ctr := cc |>, ctr).

  Definition do_spawn {Mailbox : Set} (parent : PID) (prog : @Program Mailbox) (v : VM) : VM :=
    let (v, child_pid_suffix) := new_child_id parent v in
    let rq := runq v in
    let new_pid := parent ++ [child_pid_suffix] in
    let new_process := {| proc_mb_t := Mailbox; proc_prog := prog |} in
    let w' := h_spawn new_pid Mailbox (world v) in
    v<| runq := (new_pid, new_process) :: rq|> <|world := w'|>.

  Definition initVm {Mailbox : Set} (w : World) (p : @Program Mailbox) :=
    let vm :=
      {|
        world := w;
        runq := [];
        sleepq := [];
        child_ctr := Pid.FMap.empty _;
      |} in
    do_spawn [] p vm.
End VM.

Global Arguments VM {_ _} _.
Global Arguments p_dead {_ _ _}.
Global Arguments p_yield {_ _ _}.
Global Arguments p_cont {_ _ _}.
Global Arguments p_spawn {_ _ _ _}.

(* begin details *)
Notation "'do' V '<-' I ; C" := (p_cont (I) (fun V => C))
    (at level 100, C at next level, V name, right associativity) : slot_scope.

Notation "'done'" := (p_cont (fun _ => p_dead))
    (at level 100, right associativity) : slot_scope.

Notation "'call' V '<-' I ; C" := (I (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, C at next level, V ident,
    right associativity) : slot_scope.

Notation "P '!' M ; C" := (p_cont (send P (appmsg M)) (fun _ => C))
    (at level 99, C at next level, right associativity) : slot_scope.

(* end details *)

Definition prog_t `(IOHandler) mb_t :=
  @Program Request Reply mb_t.

Section test.
  Let h := mailboxHandler.
  Let VM := VM h.

  Let child1 : prog_t h positive := p_dead.

  Let child2 : prog_t h bool := p_dead.

  Let prog : prog_t h True :=
        spawn c1 <- child1;
        c1 ! 1;
        spawn c2 <- child2;
        c2 ! false;
        p_dead.
End test.
