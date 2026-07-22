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
      h_handler (pid : Ref) (req : Request) : MFunRet (Reply req) h_state;
      h_initial : h_state;

      h_spawn (pid : Ref) (mailbox_t : Set) : h_state -> h_state;
      h_spawn_covariance : forall pid mailbox_t s s',
        s == s' ->
        h_spawn pid mailbox_t s == h_spawn pid mailbox_t s';

      h_spawn_commutativity : forall pid1 pid2 mb_t1 mb_t2 s,
        pid1 <> pid2 ->
        h_spawn pid1 mb_t1 (h_spawn pid2 mb_t2 s) == h_spawn pid2 mb_t2 (h_spawn pid1 mb_t1 s);

      h_terminate (pid : Ref) : MFun h_state h_state;

      h_terminate_commutativity (pid1 pid2 : Ref) : pid1 <> pid1 -> commute (h_terminate pid1) (h_terminate pid2);

      h_spawn_terminate_commutativity (pid1 pid2 : Ref) mb_t : pid1 <> pid2 -> commute (h_terminate pid1) (pure (h_spawn pid2 mb_t) (h_spawn_covariance pid2 mb_t));
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
