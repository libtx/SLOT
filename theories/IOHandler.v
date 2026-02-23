From Coq Require Import
  List
  ZArith
  SetoidClass.

From SLOT Require Import
  Setoids
  TransitionSystem
  Pid.

From Hammer Require Import
  Tactics.

Section IOHandler.
  Context {Request : Type} {Reply : Request -> Type}.

  Definition MFunRet Ret State `{HRet : Setoid Ret} `{HState : Setoid State} :=
    @MFun State (Ret * State) HState (@pair_setoid _ _ HRet HState).

  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_handler (pid : PID) (req : Request) : MFunRet (Reply req) h_state;

      h_spawn (pid : PID) (mailbox_t : Set) : h_state -> h_state;
      h_terminate (pid : PID) : h_state -> h_state;
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
