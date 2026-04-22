From Stdlib Require Import
  List
  ZArith
  SetoidClass.

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
End mailbox.

Section IOHandler.
  Context {Request : Type} {Reply : Request -> Type}.

  Class IOHandlerBlocks (VM World : Type) `{iohm_setoid : Setoid VM} := {
      lift_w_ret {Ret World : Type} `{Heqiv_r : Setoid Ret} `{Hequiv_w : Setoid World}
        (w_morph : @MFunRet Ret World Heqiv_r Hequiv_w) : @MFunRet Ret VM Heqiv_r iohm_setoid;

      lift_w {World : Type} `{Hequiv_w : Setoid World}
        (w_morph : @MFun World World Hequiv_w Hequiv_w) : @MFun VM VM iohm_setoid iohm_setoid;

      make_ref : @MFunRet Ref VM _ iohm_setoid;
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

      h_spawn_commutativity : forall pid1 pid2 mb_t1 mb_t2 s,
        pid1 <> pid2 ->
        h_spawn pid1 mb_t1 (h_spawn pid2 mb_t2 s) == h_spawn pid2 mb_t2 (h_spawn pid1 mb_t1 s);

      h_terminate (pid : Ref) : MFun h_state h_state;
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
