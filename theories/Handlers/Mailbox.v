From Coq Require Import
  Classes.EquivDec
  SetoidClass
  Classes.SetoidDec.

Require Import
  Queue
  Multifunction
  Pid
  IOHandler.

From Hammer Require Import
  Tactics.

Section defn.
  Inductive Message {AppMessage} :=
  | appmsg : AppMessage -> Message.

  (** Contents of the mailbox *)
  Record Mailbox := {
      mb_t : Type;
      mb_q : @Queue (@Message mb_t);
    }.

  (** Handler state *)
  Let t := Pid.FMap.t Mailbox.

  (** "Address" of the mailbox *)
  Record Address {mba_t : Set} := {
      mba_pid : PID;
      (* Address record carries the proof that the mailbox of
      [mba_pid] process is what we expect. This information is used at
      the compile time for type checking. *)
      mba_t_proof (mboxes : t) :
      match Pid.FMap.find mba_pid mboxes with
      | None => True
      | Some {| mb_t := t |} => t = mba_t
      end
    }.

  Inductive MBReq : Type :=
  | send {T : Set} : @Message T -> @Address T -> MBReq.

  Definition MBRet (req : MBReq) : Type :=
    match req with
    | send _ _ => True
    end.

  Definition do_send_msg {T : Set} (msg : @Message T) (to : @Address T) (mboxes : t) : t.
    destruct to as [pid HpidT].
    remember (Pid.FMap.find pid mboxes) as mb.
    destruct mb as [mbox|].
    - specialize (HpidT mboxes). rewrite <-Heqmb in HpidT.
      destruct mbox as [mb_t mb_q].
      subst.
      set (mbox' := {| mb_t := T; mb_q := push msg mb_q |}).
      exact (Pid.FMap.add pid mbox' mboxes).
    - exact mboxes.
  Defined.

  Program Definition send_ {T : Set} (msg : @Message T) (to : @Address T) : MFunRet True t :=
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

  (* Let mailboxes_equiv := @Pid.FMap.Equiv Mailbox queue_equiv. *)

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      (* TODO: Use a setoid via mailboxes_equiv *)
      h_setoid := eq_setoid _;
      h_handler _ req := mailbox_step req
    |}.
End defn.
