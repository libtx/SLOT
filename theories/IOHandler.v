From Coq Require Import
  List
  ZArith
  SetoidClass.

From SLOT Require Import
  Setoids
  TransitionSystem
  Ref.

From Hammer Require Import
  Tactics.

Section IOHandler.
  Context {Request : Type} {Reply : Request -> Type}.

  Definition MFunRet Ret State `{HRet : Setoid Ret} `{HState : Setoid State} :=
    @MFun State (Ret * State) HState (@pair_setoid _ _ HRet HState).


  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_handler (pid : Ref) (req : Request) : MFunRet (Reply req) h_state;
      h_initial : h_state;

      h_spawn (pid : Ref) (mailbox_t : Set) : h_state -> h_state;
      h_spawn_covariance : forall pid mailbox_t s s',
        s == s' ->
        h_spawn pid mailbox_t s == h_spawn pid mailbox_t s';
      h_terminate (pid : Ref) : h_state -> h_state;
      h_terminate_covariance : forall pid s s',
        s == s' ->
        h_terminate pid s == h_terminate pid s';
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
