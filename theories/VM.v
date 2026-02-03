From Coq Require Import
  List
  ZArith
  SetoidClass.
Import ListNotations.

From SLOT Require Import
  Multifunction
  Pid.

From Hammer Require Import
  Tactics.

Section IOHandler.
  Context {Request : Type} {Reply : Request -> Type}.

  Definition MFunRet Ret State `{HRet : Setoid Ret} `{HState : Setoid State} :=
    @MFun State (Ret * State) HState (@setoidPair _ _ HRet HState).

  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_handler (pid : PID) (req : Request) : MFunRet (Reply req) h_state;
    }.
End IOHandler.


Section Thread.
  Context `{H : IOHandler}.

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

  Record Thread :=
    mkThread
    { (* Continuation *)
      t_prog : Program;
      (* Number of children spawned by the thread that is used to
      generate PID of its children: *)
      t_last_child : positive
    }.
End Thread.

Section VM.
  Context `{H : IOHandler}.
  Let T := @Thread Request Reply.
  Definition Threads := Pid.FMap.t T.

  Record VM :=
    { threads : Threads;
      world : @h_state _ _ H;
    }.
End VM.
(*
  Print Setoid.

  Program Instance vmSetoid : Setoid VM :=
    {| equiv (a b : VM) := equiv _ _ (world a) (world b);
    |}.




  Program Definition vm_step : MFun VM VM :=
    {|
    |}

  Definition step (pid : PID) : Threads -> Threads :=
    match ThreadsMap.

  Definition do_spawn pid lc cont child rest :=
    let new_pid := pid ++ [lc] in
    let this_thread := {| t_pid := pid;
                          t_last_child := Pos.succ lc;
                          t_prog := cont new_pid
                       |} in
    let new_thread := {| t_pid := new_pid;
                         t_last_child := 1;
                         t_prog := child
                      |} in
    this_thread :: new_thread :: rest.

  Definition do_io pid lc req (ret : Reply req) cont rest :=
    let new_thread := {| t_pid := pid;
                         t_last_child := lc;
                         t_prog := cont ret
                      |} in
    new_thread :: rest.

  Definition do_yield {CTX : Type} pid lc (ctx : CTX) (cont : CTX -> Program) rest :=
    let new_thread := {|
                       t_pid := pid;
                       t_last_child := lc;
                       t_prog := cont ctx
                     |} in
    new_thread :: rest.

  Definition ProcessStep (t : Thread) (threads : list Thread) (w w' : @h_state _ _ H) : Prop :=
    match t_prog t with
    | p_dead =>
        w = w' /\ threads = []
    | p_yield ctx cont =>
        w = w' /\ threads = [{| t_pid := t_pid t; t_last_child := t_last_child t; t_prog := cont ctx|} ]
    | p_spawn child cont =>
        let lc := t_last_child t in
        let new_pid := t_pid t ++ [lc] in
        let new := {| t_pid := new_pid; t_last_child := 1; t_prog := child |} in
        let t' := {| t_pid := t_pid t; t_last_child := Pos.succ lc; t_prog := cont new_pid |} in
        w = w' /\ threads = [t'; new]
    | _ =>
        False
    end.

  Inductive VMStep : relation VM :=
  | vm_step : forall threads thread threads' threads'' world world',
      Pick threads thread threads' ->
      ProcessStep thread threads'' world world' ->
      VMStep {| threads := threads;
               world := world;
             |}
             {| threads := threads'';
               world := world'
             |}.


  (* Inductive VMStep : relation VM := *)
  (* | vm_proc_down : forall pid lc threads threads' world, *)
  (*     Pick threads ({| t_pid := pid; t_last_child := lc; t_prog := p_dead |}, threads') -> *)
  (*     VMStep {| threads := threads; *)
  (*               world := world *)
  (*            |} *)
  (*            {| threads := threads'; *)
  (*               world := world *)
  (*            |} *)
  (* | vm_proc_yield : forall pid lc CTX ctx cont threads threads' world, *)
  (*     Pick threads ({| t_pid := pid; t_last_child := lc; t_prog := @p_yield CTX ctx cont |}, threads') -> *)
  (*     VMStep {| threads := threads; *)
  (*               world := world *)
  (*            |} *)
  (*            {| threads := do_yield pid lc ctx cont threads'; *)
  (*                world := world *)
  (*            |} *)
  (* | vm_proc_spawn : forall pid lc cont child threads threads' world, *)
  (*     Pick threads ({| t_pid := pid; t_last_child := lc; t_prog := p_spawn child cont |}, threads') -> *)
  (*     VMStep {| threads := threads; *)
  (*               world := world *)
  (*            |} *)
  (*            {| threads := do_spawn pid lc cont child threads'; *)
  (*               world := world *)
  (*            |} *)
  (* | vm_proc_io : forall pid lc req ret cont threads threads' world world', *)
  (*     Pick threads ({| t_pid := pid; t_prog := p_cont req cont; t_last_child := lc |}, threads') -> *)
  (*     world ~[h_handler pid req]~> (ret, world') -> *)
  (*     VMStep {| threads := threads; *)
  (*               world := world *)
  (*            |} *)
  (*            {| threads := do_io pid lc req ret cont threads'; *)
  (*               world := world' *)
  (*            |}. *)

  Program Instance vmEquiv : Setoid VM :=
    {| equiv a b :=
        Permutation (threads a) (threads b) /\ @equiv _ h_setoid (world a) (world b)
    |}.
  Next Obligation.
  Admitted.

  Program Definition mfunVM : @MFun VM VM vmEquiv vmEquiv :=
    {| morphism := VMStep;
    |}.
  Next Obligation.
  Admitted.

  (* FIXME *)
  Fixpoint pid_order (a b : PID) : Prop :=
    match a, b with
    | [], [] => True
    | [], _ => False
    | _, [] => True
    | a :: resta, b :: restb =>
        pid_order resta restb
    end.

  Fail Definition vm_step_order (a b : VMStep) : Prop  := False.

  Definition initVM (world : h_state) (threads : list Program) : VM :=
    {|
      world := world;

      threads :=
        let go (acc : positive * list Thread) (prog : Program) :=
          let (pid, threads) := acc in
          let thread := {| t_pid := [pid]; t_prog := prog; t_last_child := 1 |} in
          (Pos.succ pid, thread :: threads) in
        let (_, threads) := fold_left go threads (1%positive, []) in
        threads;
    |}.

  Let mfun := @MFun VM VM vmEquiv vmEquiv.

  Inductive VMEnsemble : VM -> TraceEnsemble :=
  | vm_nil : forall w,
      VMEnsemble {| world := w; threads := [] |} []
  | vm_cons : forall (s s' : VM) (t : list mfun),
      s ~[mfunVM]~> s' ->
      VMEnsemble s' t ->
      VMEnsemble s (mfunVM :: t).
End VM.

Global Arguments initVM {_ _} (_ _ _).

Definition ProgramType {Req Ret} (_ : @IOHandler Req Ret) : Type := @Program Req Ret.

Notation "'do' V '<-' I ; C" := (p_cont (I) (fun V => C))
    (at level 100, C at next level, V name, right associativity) : slot_scope.

Notation "'done'" := (p_dead)
    (at level 100, right associativity) : slot_scope.

Notation "'call' V '<-' I ; C" := (I (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity,
      only parsing) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, C at next level, V ident,
      right associativity) : slot_scope.

Section test.
  Let handler := storageHandler nat nat listStorage _ _.

  Let getter (key : nat) : ProgramType handler :=
        do val <- get key;
        done.

  Let prog : ProgramType handler :=
        spawn A <- getter 1;
        spawn B <- getter 2;
        done.

  Let initialState := initVM handler [] [prog].

  Goal forall t,
      VMEnsemble (initVM handler [] []) t ->
      t = [].
  Proof.
    intros t Ht.
    inversion Ht.
    - reflexivity.
    - subst. simpl in H. inversion H. subst. inversion H3.
  Qed.

  Goal forall t s s',
      VMEnsemble (initVM handler [] []) t ->
      (* s ~[map (ts_mfun t)]~> s' -> *)
      CanonicalTrace t s s'.

  (*
Cannot infer the implicit parameter canon_rel of mfunCanonTrace whose type is "relation (MFun VM VM)" in
environment:
handler := storageHandler nat nat listStorage eq_equivalence EqDec.nat_eq_eqdec : IOHandler
getter := fun key : nat => do _ <- get key; (done) : nat -> ProgramType handler
prog := spawn _ <- getter 1; (spawn _ <- getter 2; (done)) : ProgramType handler
initialState := initVM handler [] [prog] : VM
t : list (MFun VM VM)
   *)

  Ltac inv A := inversion A; subst.

  Goal forall w',
      VMStep initialState w' ->
      False.
  Proof.
    intros w' H.
    inv H.
    inv H2.
    - destruct H4 as [Hw' Ht'].
      subst. simpl in H.
      inv


    - inversion H1.
  Qed.


    unfold initialState, prog, getter.
    intros w' H.
    inversion H; subst.
    inversion H2; subst.
    - inversion H4.

    - inversion H3. subst. inversion H1.
    - inversion H3. subst. inversion H1.
    - inversion H3. subst.
      +




  Goal forall t,
      VMEnsemble initialState t ->
      (* initialState ~[@mfunCanonTrace _ _ (fun a b => True) t]~> initVM handler [] [] -> *)
      t = [].
  Proof.
    intros t Ht.
    inversion Ht.
    intros t Ht Ht'.
    unfold initialState, initVM.
    intros t Ht.
    inversion_clear Ht.
    - simpl in H.

End test.
*)
