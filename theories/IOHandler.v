From Stdlib Require Import
  List
  ZArith
  SetoidClass.

Import ListNotations.

From SLOT Require Import
  Setoids
  TransitionSystem
  Ref
  Queue.

From Hammer Require Import
  Tactics.

(** * Abstract pid-allocation contexts

    A [Context] is an abstract collection of allocated pids.  Instead
    of exposing the raw reference-counter collection, it provides two
    tests, [is_valid_pid] and [is_invalid_pid], which are proper
    morphisms: they respect equality of contexts, so validity of a pid
    can be transported along setoid-equal contexts. *)

Definition Pid := Ref.

Section ctx.
  Class VMContext (T : Type) := {
      ctx_setoid :: Setoid T;

      is_valid_pidb : Pid -> T -> bool;

      is_valid_pidb_proper :
        forall pid, Proper (equiv ==> eq) (is_valid_pidb pid);
    }.

  Context `{Hctx : VMContext}.

  Definition is_valid_pid (pid : Pid) (ctx : T) : Prop :=
    is_valid_pidb pid ctx = true.

  Definition is_invalid_pid (pid : Pid) (ctx : T) : Prop :=
    is_valid_pidb pid ctx = false.

  Add Parametric Morphism (pid : Pid) : (is_valid_pid pid) with
    signature equiv ==> iff as is_valid_pid_proper.
  Proof.
    intros ctx ctx' Hequiv.
    unfold is_valid_pid.
    split; intros H;
      specialize (is_valid_pidb_proper pid ctx ctx' Hequiv) as H'.
    - now rewrite <-H'.
    - now rewrite H'.
  Qed.

  Add Parametric Morphism (pid : Pid) : (is_invalid_pid pid) with
    signature equiv ==> iff as is_invalid_pid_proper.
  Proof.
    intros ctx ctx' Hequiv.
    unfold is_invalid_pid.
    split; intros H;
      specialize (is_valid_pidb_proper pid ctx ctx' Hequiv) as H'.
    - now rewrite <-H'.
    - now rewrite H'.
  Qed.
End ctx.

Section mailbox.
  Inductive Message {AppMessage} :=
  | appmsg : AppMessage -> Message.

  (** Contents of the mailbox *)
  Record Mailbox := {
      mb_t : Set;
      mb_q : @Queue (@Message mb_t);
    }.

  (** Handler state *)
  Let t := Ref.FMap.M.t Mailbox.

  (** "Address" of the mailbox *)
  Record Address {mba_t : Set} :=
    mkAddress
    {
      mba_pid : Ref
    }.

  Definition node_of {mba_t} (a : @Address mba_t) : option positive :=
    let fix go prev l :=
      match l with
      | [] => prev
      | (a :: l) => go a l
      end in
    match a with
    | {| mba_pid := [] |} => None
    | {| mba_pid := (a :: l) |} => Some (go a l)
    end.
End mailbox.

Section IOHandler.
  Context {Ctx : Type} `{HCtx : VMContext Ctx}.
  Context {Request : Type} {Reply : Request -> Type}.

  (** A context packaged with a proof that [pid] is valid in it: the
      parameter space of [h_perform_io] and [h_terminate]. *)
  Definition pid_valid_in (pid : Pid) : Type :=
    {ctx : Ctx & is_valid_pid pid ctx}.

  (** A context packaged with a proof that [pid] is not yet valid in
      it: the parameter space of [h_spawn]. *)
  Definition pid_fresh_in (pid : Pid) : Type :=
    {ctx : Ctx & is_invalid_pid pid ctx}.

  (** Two context packages are [same_pid_status] when their contexts are
      setoid-equal; the carried proofs are not compared. *)
  Definition same_pid_status {P : Ctx -> Prop} :
      forall c c' : {ctx : Ctx & P ctx}, Prop :=
    fun c c' => projT1 c == projT1 c' : Prop.

  (** ** The basic operations of an I/O handler

      [IOHandler_basics] bundles the handler state together with the
      world-level operations.  It carries no laws: those live in
      [IOHandler], which extends a basics implementation. *)

  Class IOHandler_basics := {
      h_state : Type;
      h_setoid : Setoid h_state;

      (** [h_perform_io] is only applied to pids that are valid in
          the context [ctx] of the world it runs in: *)
      h_perform_io (pid : Pid) (ctx : Ctx) (pid_valid : is_valid_pid pid ctx)
        (req : Request) : MFunRet (Reply req) h_state h_state;
      h_initial : h_state;

      (** [h_spawn] creates a mailbox for a pid that is NOT yet valid
          in [ctx]: [ctx] is the pre-allocation pid collection, and
          the fresh pid becomes valid only after the spawn. *)
      h_spawn (pid : Pid) (ctx : Ctx) (pid_fresh : is_invalid_pid pid ctx)
        (mailbox_t : Set) : MFun h_state h_state;

      h_terminate (normal : bool) (pid : Pid) (ctx : Ctx)
        (pid_valid : is_valid_pid pid ctx) : MFun h_state h_state;
    }.


End IOHandler.

Definition h_request_t `(IOHandler_basics) : Type := Request.
Definition h_reply_t `(IOHandler_basics) : Request -> Type := Reply.
