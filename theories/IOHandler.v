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

  Class IOHandler := {
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

      h_spawn_commutativity : forall (pid1 pid2 : Pid) (mb_t1 mb_t2 : Set)
                                     (ctx1 : Ctx) (fresh1 : is_invalid_pid pid1 ctx1)
                                     (ctx2 : Ctx) (fresh2 : is_invalid_pid pid2 ctx2),
        pid1 <> pid2 ->
        forall s0 s1 s2,
          s0 ~[h_spawn pid1 ctx1 fresh1 mb_t1]~> s1 ->
          s1 ~[h_spawn pid2 ctx2 fresh2 mb_t2]~> s2 ->
          forall (ctx2' : Ctx) (fresh2' : is_invalid_pid pid2 ctx2')
                 (ctx1' : Ctx) (fresh1' : is_invalid_pid pid1 ctx1'),
            exists{s2' == s2}, exists s1',
              s0 ~[h_spawn pid2 ctx2' fresh2' mb_t2]~> s1' /\
              s1' ~[h_spawn pid1 ctx1' fresh1' mb_t1]~> s2';

      h_terminate (normal : bool) (pid : Pid) (ctx : Ctx)
        (pid_valid : is_valid_pid pid ctx) : MFun h_state h_state;

      (** The world-level effects must not depend on the choice of the
          context: setoid-equal contexts must lead to setoid-equal
          results.  These laws make it possible to relate the effects
          performed from setoid-equal VM states, whose contexts may
          differ syntactically. *)

      h_perform_io_ctx_covariance :
        forall (pid : Pid) (req : Request)
               (ctx ctx' : Ctx)
               (valid : is_valid_pid pid ctx)
               (valid' : is_valid_pid pid ctx'),
          ctx == ctx' ->
          forall s s' (ret : Reply req * h_state),
            s == s' ->
            s ~[h_perform_io pid ctx valid req]~> ret ->
            exists{ret' == ret}, s' ~[h_perform_io pid ctx' valid' req]~> ret';

      h_spawn_ctx_covariance :
        forall (pid : Pid) (mb_t : Set)
               (ctx ctx' : Ctx)
               (fresh : is_invalid_pid pid ctx)
               (fresh' : is_invalid_pid pid ctx'),
          ctx == ctx' ->
          forall s s' s2,
            s == s' ->
            s ~[h_spawn pid ctx fresh mb_t]~> s2 ->
            exists{s2' == s2}, s' ~[h_spawn pid ctx' fresh' mb_t]~> s2';

      h_terminate_ctx_covariance :
        forall (normal : bool) (pid : Pid)
               (ctx ctx' : Ctx)
               (valid : is_valid_pid pid ctx)
               (valid' : is_valid_pid pid ctx'),
          ctx == ctx' ->
          forall s s' s2,
            s == s' ->
            s ~[h_terminate normal pid ctx valid]~> s2 ->
            exists{s2' == s2}, s' ~[h_terminate normal pid ctx' valid']~> s2';

      (** This property specifies that termination of a process cannot
          interfere with spawning of any new process.  The two pids
          must be distinct; the effects themselves do not depend on
          the choice of the contexts witnessing validity/freshness
          (cf. [h_spawn_commutativity]). *)
      h_spawn_terminate_commutativity :
        forall (normal : bool) (pid1 pid2 : Pid) (mb_t : Set)
               (ctx1 : Ctx) (valid1 : is_valid_pid pid1 ctx1)
               (ctx2 : Ctx) (fresh2 : is_invalid_pid pid2 ctx2),
          pid1 <> pid2 ->
          (forall s0 s1 s2,
             s0 ~[h_terminate normal pid1 ctx1 valid1]~> s1 ->
             s1 ~[h_spawn pid2 ctx2 fresh2 mb_t]~> s2 ->
             forall (ctx2' : Ctx) (fresh2' : is_invalid_pid pid2 ctx2')
                    (ctx1' : Ctx) (valid1' : is_valid_pid pid1 ctx1'),
               exists{s2' == s2}, exists s1',
                 s0 ~[h_spawn pid2 ctx2' fresh2' mb_t]~> s1' /\
                 s1' ~[h_terminate normal pid1 ctx1' valid1']~> s2')
          /\
          (forall s0 s1 s2,
             s0 ~[h_spawn pid2 ctx2 fresh2 mb_t]~> s1 ->
             s1 ~[h_terminate normal pid1 ctx1 valid1]~> s2 ->
             forall (ctx1' : Ctx) (valid1' : is_valid_pid pid1 ctx1')
                    (ctx2' : Ctx) (fresh2' : is_invalid_pid pid2 ctx2'),
               exists{s2' == s2}, exists s1',
                 s0 ~[h_terminate normal pid1 ctx1' valid1']~> s1' /\
                 s1' ~[h_spawn pid2 ctx2' fresh2' mb_t]~> s2');
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
