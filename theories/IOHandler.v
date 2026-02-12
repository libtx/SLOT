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
    }.
End IOHandler.
