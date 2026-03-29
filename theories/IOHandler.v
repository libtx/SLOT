From Stdlib Require Import
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

  Class IOHandlerMonad (VM : Type) := {
      iohm_setoid : Setoid VM;

      lift_w_ret {Ret State : Type} `{Heqiv_r : Setoid Ret}
        (w_morph : @MFunRet Ret State Heqiv_r Heqiv_w) : @MFunRet Ret VM Heqiv_r vm_setoid;
    }.

  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_handler (pid : Ref) (req : Request) : MFunRet (Reply req) h_state;
      h_initial : h_state;

      h_spawn (pid : Ref) (mailbox_t : Set) : h_state -> h_state;
      h_spawn_covariance : forall pid mailbox_t s s',
        s == s' ->
        h_spawn pid mailbox_t s == h_spawn pid mailbox_t s';

      h_terminate (pid : Ref) : MFun h_state h_state;
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
