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

Import Ref.FMap.

From Hammer Require Import
  Tactics.

(** A pid is valid (its reference was already allocated) in the
    reference counter collection [cc]. *)
Definition is_valid_pid (pid : Ref) (cc : Fresh.t) : Prop :=
  Fresh.is_valid_ref pid cc = true.

(** A pid is not yet allocated in [cc]. *)
Definition is_invalid_pid (pid : Ref) (cc : Fresh.t) : Prop :=
  Fresh.is_valid_ref pid cc = false.

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
  Context {Request : Type} {Reply : Request -> Type}.

  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;

      (** [h_handler] is only applied to pids that are valid in the
          reference counter collection [rc] of the world it runs in: *)
      h_handler (pid : Ref) (rc : Fresh.t) (pid_valid : is_valid_pid pid rc)
        (req : Request) : MFunRet (Reply req) h_state h_state;
      h_initial : h_state;

      (** [h_spawn] creates a mailbox for a pid that is NOT yet valid
          in [rc]: [rc] is the pre-allocation pid collection, and the
          fresh pid becomes valid only after the spawn. *)
      h_spawn (pid : Ref) (rc : Fresh.t) (pid_fresh : is_invalid_pid pid rc)
        (mailbox_t : Set) : MFun h_state h_state;

      h_spawn_commutativity : forall (pid1 pid2 : Ref) (mb_t1 mb_t2 : Set)
                                     (rc1 : Fresh.t) (fresh1 : is_invalid_pid pid1 rc1)
                                     (rc2 : Fresh.t) (fresh2 : is_invalid_pid pid2 rc2),
        pid1 <> pid2 ->
        forall s0 s1 s2,
          s0 ~[h_spawn pid1 rc1 fresh1 mb_t1]~> s1 ->
          s1 ~[h_spawn pid2 rc2 fresh2 mb_t2]~> s2 ->
          forall (rc2' : Fresh.t) (fresh2' : is_invalid_pid pid2 rc2')
                 (rc1' : Fresh.t) (fresh1' : is_invalid_pid pid1 rc1'),
            exists{s2' == s2}, exists s1',
              s0 ~[h_spawn pid2 rc2' fresh2' mb_t2]~> s1' /\
              s1' ~[h_spawn pid1 rc1' fresh1' mb_t1]~> s2';

      h_terminate (normal : bool) (pid : Ref) (rc : Fresh.t)
        (pid_valid : is_valid_pid pid rc) : MFun h_state h_state;

      (** The world-level effects must not depend on the choice of the
          reference-counter collection: collections that are
          setoid-equal (they agree on all [get]s) must lead to
          setoid-equal results.  These laws make it possible to relate
          the effects performed from setoid-equal VM states, whose
          reference counters may differ syntactically. *)

      h_handler_rc_covariance :
        forall (pid : Ref) (req : Request)
               (rc rc' : Fresh.t)
               (valid : is_valid_pid pid rc)
               (valid' : is_valid_pid pid rc'),
          rc == rc' ->
          forall s s' (ret : Reply req * h_state),
            s == s' ->
            s ~[h_handler pid rc valid req]~> ret ->
            exists{ret' == ret}, s' ~[h_handler pid rc' valid' req]~> ret';

      h_spawn_rc_covariance :
        forall (pid : Ref) (mb_t : Set)
               (rc rc' : Fresh.t)
               (fresh : is_invalid_pid pid rc)
               (fresh' : is_invalid_pid pid rc'),
          rc == rc' ->
          forall s s' s2,
            s == s' ->
            s ~[h_spawn pid rc fresh mb_t]~> s2 ->
            exists{s2' == s2}, s' ~[h_spawn pid rc' fresh' mb_t]~> s2';

      h_terminate_rc_covariance :
        forall (normal : bool) (pid : Ref)
               (rc rc' : Fresh.t)
               (valid : is_valid_pid pid rc)
               (valid' : is_valid_pid pid rc'),
          rc == rc' ->
          forall s s' s2,
            s == s' ->
            s ~[h_terminate normal pid rc valid]~> s2 ->
            exists{s2' == s2}, s' ~[h_terminate normal pid rc' valid']~> s2';

      (* (** This property specifies that termination of a process cannot *)
      (* interfere with spawning of any new process: *) *)
      (* h_spawn_terminate_commutativity (normal : bool) (pid1 pid2 : Ref) mb_t rc1 rc2 : *)
      (*   is_valid_pid pid1 rc1 -> *)
      (*   is_invalid_pid pid2 rc2 -> *)
      (*   commute (h_terminate normal pid1 rc1 _) (h_spawn pid2 rc2 _ mb_t); *)
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
