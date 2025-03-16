From Coq Require Import
  Relation_Definitions
  List
  ZArith
  SetoidClass.
Import ListNotations.

From SLOT Require Import
  Multifunction.

From Hammer Require Import
  Tactics.

Definition PID : Set := list positive.

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

From LibTx Require Storage.
Module stor := LibTx.Storage.Classes.

From LibTx Require Import
  Instances.List.

From Coq Require
  Classes.EquivDec.

Module EqDec := EquivDec.

Section storage_handler.
  Context {Key Val Container : Type} `(Hstor : stor.Storage Key Val Container) `{Heqdec : EqDec.EqDec Key eq}.

  Inductive StorageReq : Type :=
  | get : Key -> StorageReq
  | put : Key -> Val -> StorageReq
  | delete : Key -> StorageReq.

  Definition StorageRet (req : StorageReq) : Type :=
    match req with
    | get k => option Val
    | put k v => True
    | delete k => True
    end.

  Program Definition storage_get (k : Key) : MFunRet (option Val) Container :=
    {| morphism s x :=
         x = (stor.get k s, s)
    |}.
  Next Obligation.
    sauto.
  Qed.

  Program Definition storage_put (k : Key) (v : Val) : MFunRet True Container :=
    {| morphism s x :=
         x = (I, stor.put k v s)
    |}.
  Next Obligation.
    exists (I, stor.put k v x'). split.
    - reflexivity.
    - destruct t. split.
      + reflexivity.
      + now rewrite H.
  Qed.

  Program Definition storage_delete (k : Key) : MFunRet True Container :=
    {| morphism s x :=
        x = (I, stor.delete k s)
    |}.
  Next Obligation.
    exists (I, stor.delete k x'). split.
    - reflexivity.
    - destruct t. split.
      + reflexivity.
      + now rewrite H.
  Qed.

  Definition StorageStep (req : StorageReq) : MFunRet (StorageRet req) Container :=
    match req with
    | get k => storage_get k
    | put k v => storage_put k v
    | delete k => storage_delete k
    end.

  Instance storageHandler : @IOHandler StorageReq StorageRet :=
    {|
      h_state := Container;
      h_setoid := stor.s_eq_setoid;
      h_handler _ req := StorageStep req
    |}.
End storage_handler.

Global Arguments storageHandler (_ _) {_} (_).

From Coq Require Import
  Sorting.Permutation.
From SLOT Require Import
  ListSelector.

Section VM.
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
    { (* PID of the thread: *)
      t_pid : PID;
      (* Continuation *)
      t_prog : Program;
      (* Number of children spawned by the thread that is used to
      generate PID of its children: *)
      t_last_child : positive
    }.

  Record VM :=
    { threads : list Thread;
      world : @h_state _ _ H;
    }.

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

  Inductive VMStep : relation VM :=
  | vm_proc_down : forall pid lc threads threads' world,
      Pick threads ({| t_pid := pid; t_last_child := lc; t_prog := p_dead |}, threads') ->
      VMStep {| threads := threads;
                world := world
             |}
             {| threads := threads';
                world := world
             |}
  | vm_proc_yield : forall pid lc CTX ctx cont threads threads' world,
      Pick threads ({| t_pid := pid; t_last_child := lc; t_prog := @p_yield CTX ctx cont |}, threads') ->
      VMStep {| threads := threads;
                world := world
             |}
             {| threads := do_yield pid lc ctx cont threads';
                 world := world
             |}
  | vm_proc_spawn : forall pid lc cont child threads threads' world,
      Pick threads ({| t_pid := pid; t_last_child := lc; t_prog := p_spawn child cont |}, threads') ->
      VMStep {| threads := threads;
                world := world
             |}
             {| threads := do_spawn pid lc cont child threads';
                world := world
             |}
  | vm_proc_io : forall pid lc req ret cont threads threads' world world',
      Pick threads ({| t_pid := pid; t_prog := p_cont req cont; t_last_child := lc |}, threads') ->
      world ~[h_handler pid req]~> (ret, world') ->
      VMStep {| threads := threads;
                world := world
             |}
             {| threads := do_io pid lc req ret cont threads';
                world := world'
             |}.

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

  Check mfun_morph_rel.

  (* Definition vm_step_order :  := *)
  (*   let pid1 := match a with *)
  (*               | vm_proc_down pid _ _ _ _ _ => pid *)
  (*               end in *)
  (*   True. *)

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
      initialState ~[compose_list t]~> initVM handler [] [] ->
      t = [].
  Proof.
    intros t Ht.
    Fail apply canonicalize_trace in Ht.
    unfold initialState, initVM in Ht.
  Abort.
End test.
