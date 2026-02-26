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
  Hammer.

From RecordUpdate Require Import
  RecordUpdate.

Open Scope positive_scope.

Section VM.
  Context `{IOH : IOHandler} {AppMessage : Type}.

  Let World := @h_state _ _ IOH.

  CoInductive Program (Mailbox : Set) : Type :=
  | die : (* Program termintes *)
      Program Mailbox
  | p_yield :
    (** Interrupt the computation without producing any side effects.

        This primitive is used to softly introduce the concept of
        Erlang's "reductions", and to side-step termination checker,
        making programs non-Turing in a practically useful, as opposed
        to forced, way.

        In Erlang, reduction counting improves responsiveness of the
        system, in SLOT it *additionally* gives a structural argument
        "for free". *)
    forall (continuation : Program Mailbox),
      Program Mailbox
  | p_io : (* Program is doing I/O *)
    forall (pending_req : Request)
      (continuation : Reply pending_req -> Program Mailbox),
      Program Mailbox
  | p_spawn : (* Spawn a new process: *)
    forall {Mailbox' : Set}
      (child : @Program Mailbox')
      (continuation : @Address Mailbox' -> Program Mailbox),
      Program Mailbox.

  Record Process :=
    mkProcess
      { pid : PID;
        proc_mb_t : Set;
        cont : @Program proc_mb_t;
      }.

  #[export] Instance etaProc : Settable _ := settable! mkProcess <pid; proc_mb_t; cont>.

  Record VM :=
    mkVM
      { (* State of the I/O handler *)
        world : World;
        (* Set of runnable processes *)
        runq : list Process;
        (* Counter that gets incremented when process spawns a child.
        This counter is used as a suffix of the child's pid *)
        child_ctr : Pid.FMap.t positive;
      }.

  #[export] Instance etaVM : Settable _ := settable! mkVM <world; runq; child_ctr>.

  Global Program Definition vm_setoid : Setoid VM :=
    {| equiv a b :=
        let (w1, rq1, cc1) := a in
        let (w2, rq2, cc2) := b in
        let w_eq := @equiv _ h_setoid in
        let p_eq := @equiv _ (setoid_permutation _) in
        w_eq w1 w2 /\
          p_eq rq1 rq2 /\
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

  Definition do_spawn {Mailbox : Set} (parent : PID) (prog : @Program Mailbox) (v : VM) : (PID * VM) :=
    let (v, child_pid_suffix) := new_child_id parent v in
    let rq := runq v in
    let new_pid := parent ++ [child_pid_suffix] in
    let new_process := {|
                        pid := new_pid;
                        proc_mb_t := Mailbox;
                        cont := prog
                       |} in
    let w' := h_spawn new_pid Mailbox (world v) in
    (new_pid, v<| runq := new_process :: rq|> <|world := w'|>).

  Definition initVm {Mailbox : Set} (w : World) (p : @Program Mailbox) :=
    let vm :=
      {|
        world := w;
        runq := [];
        child_ctr := Pid.FMap.empty _;
      |} in
    let (_, vm) := do_spawn [] p vm in
    vm.

  Definition vmte_canon_rel (a b : Process) :=
    (* Order of events is canonical when pid a =< pid b: *)
    match PIDOrd.compare_ (pid a) (pid b) with
    | Gt => False
    | _ => True
    end.

  Lemma vmte_canon_rel_dec a b : Decidable.decidable (vmte_canon_rel a b).
  Proof.
    unfold Decidable.decidable, vmte_canon_rel.
    sauto.
  Qed.

  Lemma vmte_canon_rel_total a b : vmte_canon_rel a b \/ vmte_canon_rel b a.
  Proof.
    unfold Decidable.decidable, vmte_canon_rel.
    sauto use:PIDOrd.compare_asymm.
  Qed.

  Global Instance vmevCanonOrder : CanonicalOrder vmte_canon_rel :=
    { canon_rel_dec := vmte_canon_rel_dec;
      canon_rel_total := vmte_canon_rel_total;
    }.

  Definition exec_proc (proc : Process) (vm vm' : VM) : Prop :=
    match proc with
      {| pid := pid; proc_mb_t := mb_t; cont := prog |} =>
        match prog with
        | die _ =>
            vm' = vm <| world := h_terminate pid (world vm) |>
        | p_yield _ next =>
            let proc := {| pid := pid; proc_mb_t := mb_t; cont := next |} in
            vm' = vm <| runq := proc :: (runq vm) |>
        | p_io _ req next =>
            exists w' io_reply,
              let proc := {| pid := pid; proc_mb_t := mb_t; cont := next io_reply |} in
              morphism (h_handler pid req) (world vm) (io_reply, w') /\
              vm' = vm <| runq := proc :: (runq vm) |> <| world := w' |>
        | @p_spawn _ child_mb_t child_prog next =>
            let (child_pid, vm) := do_spawn pid child_prog vm in
            let addr := mkAddress child_mb_t child_pid in
            let proc := {| pid := pid; proc_mb_t := mb_t; cont := next addr |} in
            vm' = vm <| runq := proc :: (runq vm) |>
        end
    end.

  Program Definition vm_state_trans : MFun VM (@ts_ret VM Process) :=
    {|
      morphism vm ret :=
        match runq vm, ret with
        | [], None =>
            (* No runnable processes: *)
            True
        | rq, Some (te, vm') =>
            exists proc rq',
            Pick rq proc rq' /\ exec_proc proc (vm <|runq := rq'|>) vm'
        | _, _ =>
            False
        end
    |}.
  Next Obligation.
    sauto.
  Qed.
  Next Obligation.
    destruct x' as [w rq sq cctr].
    destruct rq as [|firstproc rq_].
    - exists None. sauto.
    - simpl in *.
      destruct y as [[te vm']|].
      + destruct H0 as [proc [rq' [Hrq' Hexec]]].
        destruct proc as [pid mb_t prog].
        destruct prog.
        2:{ unfold exec_proc in *.
  Admitted.

  Global Instance vmTS : @TransitionSystem VM Process :=
    { ts_state_trans := vm_state_trans;
    }.
End VM.

Global Arguments VM {_ _} _.
Global Arguments die {_ _ _}.
Global Arguments p_yield {_ _ _}.
Global Arguments p_io {_ _ _}.
Global Arguments p_spawn {_ _ _ _}.

(* begin details *)
Notation "'do' V '<-' I ; C" := (p_io (I) (fun V => C))
    (at level 100, C at next level, V name, right associativity) : slot_scope.

Notation "'call' V '<-' I ; C" := (I (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, C at next level, V ident,
    right associativity) : slot_scope.

Notation "P '!' M ; C" := (p_io (send P (appmsg M)) (fun _ => C))
    (at level 99, C at next level, right associativity) : slot_scope.
(* end details *)

Definition prog_t `(IOHandler) mb_t :=
  @Program Request Reply mb_t.

Section test.
  Let h := mailboxHandler.
  Let VM := VM h.

  Let child1 : prog_t h positive := die.

  Let child2 : prog_t h bool := die.

  Let prog : prog_t h True :=
        spawn c1 <- child1;
        c1 ! 1;
        spawn c2 <- child2;
        c2 ! false;
        die.

  Fail Let prog' : prog_t h True :=
        spawn c1 <- child1;
        c1 ! 1;
        spawn c2 <- child2;
        c2 ! 1;
        die.
End test.
