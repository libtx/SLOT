From Coq Require Import
  Classes.EquivDec
  SetoidClass
  Classes.SetoidDec.

Require Import
  Queue
  Multifunction
  Pid
  VM.

From Hammer Require Import
  Tactics.

Section defn.
  Context (AppMessage : Type).

  Inductive Message :=
  | appmsg : AppMessage -> Message.

  Definition Mailbox := @Queue Message.

  Let t := Pid.FMap.t Mailbox.

  Inductive MBReq : Type :=
  | send : Message -> PID -> MBReq.

  Definition MBRet (req : MBReq) : Type :=
    match req with
    | send _ _ => True
    end.

  Definition do_send_msg (msg : Message) (to : PID) (mboxes : t) : t :=
    match Pid.FMap.find to mboxes with
    | Some mbox =>
        Pid.FMap.add to (push msg mbox) mboxes
    | None =>
        mboxes
    end.

  Program Definition send_ (msg : Message) (to : PID) : MFunRet True t :=
    {| morphism s x :=
         x = (I, do_send_msg msg to s)
    |}.
  Next Obligation.
    sauto.
  Qed.

  Definition mailbox_step (req : MBReq) : MFunRet (MBRet req) t :=
    match req with
    | send msg to => send_ msg to
    end.

  Check Pid.FMap.Equiv.

  Let mailboxes_equiv := @Pid.FMap.Equiv Mailbox queue_equiv.

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      (* TODO: Use a setoid via mailboxes_equiv *)
      h_setoid := eq_setoid _;
      h_handler _ req := mailbox_step req
    |}.
End defn.
