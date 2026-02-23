From Coq Require Import
  Classes.EquivDec
  SetoidClass
  Classes.SetoidDec.

Require Import
  Queue
  Multifunction
  Pid
  IOHandler.

From LibTx Require Import
  Storage.

From Hammer Require Import
  Tactics.

Section defn.
  Inductive Message {AppMessage} :=
  | appmsg : AppMessage -> Message.

  (** Contents of the mailbox *)
  Record Mailbox := {
      mb_t : Set;
      mb_q : @Queue (@Message mb_t);
    }.

  (** Handler state *)
  Let t := Pid.FMap.M.t Mailbox.

  (** "Address" of the mailbox *)
  Record Address {mba_t : Set} := {
      mba_pid : PID
    }.

  (* Program Definition new_mailbox (pid : PID) (mb_t : Set) : MFun t t := *)
  (*   {| *)
  (*     morphism s s' := *)
  (*       s' = put pid {| mb_t := mb_t; mb_q := empty |} s *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   unfold exists_equiv. *)
  (*   eapply put_mor in H; try easy; try exact PIDOrd.eq_dec. *)
  (*   exists (put pid {| mb_t := mb_t0; mb_q := empty |} x'). *)
  (*   split; try reflexivity. *)
  (*   simpl in H. *)
  (*   now erewrite H. *)
  (* Qed. *)

  (* Program Definition drop_mailbox (pid : PID) : MFun t t := *)
  (*   {| *)
  (*     morphism s s' := *)
  (*       s' = delete pid s *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   unfold exists_equiv. *)
  (*   eapply delete_mor in H; try easy; try exact PIDOrd.eq_dec. *)
  (*   exists (delete pid x'). *)
  (*   split; try reflexivity. *)
  (*   simpl in H. *)
  (*   now erewrite H. *)
  (* Qed. *)

  Inductive MBReq : Type :=
  | send {T : Set} : @Address T -> @Message T -> MBReq.

  Definition MBRet (req : MBReq) : Type :=
    match req with
    | send _ _ => True
    end.

  Inductive do_send_msg : forall (Tmbox Tmsg : Set),
      PID -> @Queue (@Message Tmbox) -> @Message Tmsg ->
      t -> t -> Prop :=
  | do_send_msg_ : forall T pid msg mbox mailboxes,
      do_send_msg
        T T
        pid mbox msg
        mailboxes (put pid {| mb_t := T; mb_q := push msg mbox |} mailboxes).

  Program Definition send_ {T : Set} (msg : @Message T) (to : @Address T) : @MFunRet True t (eq_setoid _) s_eq_setoid :=
    {| morphism mboxes x :=
        let (_, mboxes') := x in
        let pid := mba_pid to in
        match @get PID Mailbox _ _ pid mboxes with
        | None =>
            mboxes' = mboxes
        | Some {| mb_t := Tmbox; mb_q := mbox |} =>
            do_send_msg Tmbox T pid mbox msg mboxes mboxes'
        end
    |}.
  Next Obligation.
    unfold exists_equiv.
  Admitted.

  Definition mailbox_step (req : MBReq) : MFunRet (MBRet req) t :=
    match req with
    | send msg to => send_ to msg
    end.

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      h_setoid := s_eq_setoid;
      h_handler _ req := mailbox_step req;
      h_spawn pid mb_t := put pid {| mb_t := mb_t; mb_q := empty |};
      h_terminate pid := delete pid;
    |}.
End defn.
