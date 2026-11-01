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

Definition Pid : Set := Ref.

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

  (** ** The basic operations of an I/O handler

      [IOHandler_basics] bundles the handler state together with the
      world-level operations.  It carries no laws: those live in
      [IOHandler], which extends a basics implementation. *)

  Class IOHandler_basics := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_initial : h_state;

      h_perform_io (pid : Pid) (req : Request) : MFunRet (Reply req) h_state h_state;

      h_spawn (pid : Pid) (mailbox_t : Set) : MFun h_state h_state;

      h_terminate (normal : bool) (pid : Pid) : MFun h_state h_state;
    }.
End IOHandler.

Definition h_request_t `(IOHandler_basics) : Type := Request.
Definition h_reply_t `(IOHandler_basics) : Request -> Type := Reply.
