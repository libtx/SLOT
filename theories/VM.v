From Coq Require Import
  List
  ZArith
  SetoidClass
  SetoidDec.
Import ListNotations.

From SLOT Require Import
  Setoids
  TransitionSystem
  Pid
  ListSelector.

From Hammer Require Import
  Tactics.

From RecordUpdate Require Import
  RecordUpdate.

Open Scope positive_scope.

Section IOHandler.
  Context {Request : Type} {Reply : Request -> Type}.

  Definition MFunRet Ret State `{HRet : Setoid Ret} `{HState : Setoid State} :=
    @MFun State (Ret * State) HState (@pair_setoid _ _ HRet HState).

  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_handler (pid : PID) (req : Request) : MFunRet (Reply req) h_state;
    }.
End IOHandler.

Section VM.
  Context `{IOH : IOHandler} {AppMessage : Type}.

  Let World := @h_state _ _ IOH.

  CoInductive Program : Type :=
  | p_dead : (* Program terminted *)
      Program
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
      (continuation : CTX -> Program),
    Program
  | p_cont : (* Program is doing I/O *)
    forall (pending_req : Request)
      (continuation : Reply pending_req -> Program),
      Program
  | p_spawn : (* Spawn a new process: *)
    forall (child : Program)
      (continuation : PID -> Program),
      Program.

  Record VM :=
    mkVM
      { (* State of the I/O handler *)
        world : World;
        (* Set of runnable processes *)
        runq : list (PID * Program);
        (* Set of sleeping processes *)
        sleepq : list (PID * Program);
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
        let p_eq := @equiv _ (setoid_permutation (PID * Program)) in
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

  Definition do_spawn (parent : PID) (prog : Program) (v : VM) : VM :=
    let (v, child_pid_suffix) := new_child_id parent v in
    let rq := runq v in
    v<| runq := (parent ++ [child_pid_suffix], prog) :: rq |>.

  Definition initVm (w : World) (p : Program) :=
    let vm :=
      {|
        world := w;
        runq := [];
        sleepq := [];
        child_ctr := Pid.FMap.empty _;
      |} in
    do_spawn [] p vm.
End VM.
