From Coq Require Import
  Classes.EquivDec
  SetoidClass
  Classes.SetoidDec.

Require Import
  Queue
  Multifunction
  Ref
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
  Let t := Ref.FMap.M.t Mailbox.

  (** "Address" of the mailbox *)
  Record Address {mba_t : Set} :=
    mkAddress
    {
      mba_pid : Ref
    }.

  Inductive MBReq : Type :=
  | send {T : Set} : @Address T -> @Message T -> MBReq.

  Definition MBRet (req : MBReq) : Type :=
    match req with
    | send _ _ => True
    end.

  Inductive dep_prop : forall A B (f : A -> Prop) a, Prop :=
  | dep_map_ : forall A f a,
      f a ->
      dep_prop A A f a.

  Inductive do_send_msg : forall (Tmbox Tmsg : Set),
      Ref -> @Queue (@Message Tmbox) -> @Message Tmsg ->
      t -> t -> Prop :=
  | do_send_msg_ : forall T pid msg mbox mailboxes,
      do_send_msg
        T T
        pid mbox msg
        mailboxes (put pid {| mb_t := T; mb_q := push msg mbox |} mailboxes).

  Lemma do_send_msg_equiv Tmbox Tmsg ref q msg a a' b :
    a == b ->
    do_send_msg Tmbox Tmsg ref q msg a a' ->
    exists b',
      do_send_msg Tmbox Tmsg ref q msg b b' /\ a' == b'.
  Admitted.

  Section send.
    Context {T : Set} (msg : @Message T) (to : @Address T).

    Definition send_morph mboxes (x : True * t) : Prop :=
       let (_, mboxes') := x in
       let pid := mba_pid to in
       match @get Ref Mailbox _ _ pid mboxes with
       | None =>
           mboxes' == mboxes
       | Some {| mb_t := Tmbox; mb_q := mbox |} =>
           do_send_msg Tmbox T pid mbox msg mboxes mboxes'
       end.

    Lemma send_morph_covariance : forall x x' y,
        x == x' ->
        send_morph x y ->
        exists{y' == y}, send_morph x' y'.
    Proof.
      unfold send_morph.
      intros x x' y Hxx' Hxy.
      replace (get (mba_pid to) x) with (get (mba_pid to) x') in Hxy by now rewrite <-Hxx'.
      destruct y as [I mboxes'].
      destruct (get (mba_pid to) x').
      - destruct m as [mb_t q].
        apply do_send_msg_equiv with (b := x') in Hxy; try assumption.
        destruct Hxy as [mboxes'' [Hxy Hmb]].
        exists (I, mboxes'').
        sauto.
      - exists (I, x).
        sauto.
    Qed.

    Definition send_  : @MFunRet True t (eq_setoid _) s_eq_setoid :=
      {|
        morphism := send_morph;
        morphism_covariance := send_morph_covariance;
      |}.
  End send.

  Definition mailbox_step (req : MBReq) : MFunRet (MBRet req) t :=
    match req with
    | send to msg => send_ msg to
    end.

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      h_setoid := s_eq_setoid;
      h_handler _ req := mailbox_step req;
      h_initial := new;
      h_spawn pid mb_t := put pid {| mb_t := mb_t; mb_q := empty |};
      h_spawn_covariance _ _ _ _ H := ltac:(now rewrite H);
      h_terminate pid := delete pid;
      h_terminate_covariance _ _ _ H := ltac:(now rewrite H);
    |}.
End defn.
