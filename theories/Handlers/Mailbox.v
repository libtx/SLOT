From Stdlib Require Import
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
  (** Handler state *)
  Let t := Ref.FMap.M.t Mailbox.

  Let mfun_t Ret := @MFunRet Ret t t (eq_setoid _) s_eq_setoid s_eq_setoid.

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

    Definition send_  : mfun_t True :=
      {|
        morphism := send_morph;
        morphism_covariance := send_morph_covariance;
      |}.
  End send.

  Definition mailbox_step (req : MBReq) : MFunRet (MBRet req) t t :=
    match req with
    | send to msg => send_ msg to
    end.

  Definition delete_mailbox (_normal : bool) (pid : Ref) : MFun t t.
    set (f := @delete _ Mailbox _ _ pid).
    refine (pure f _).
    - intros s s' H.
      rewrite H; easy.
  Defined.

  Opaque put.

  Program Definition mailbox_spawn (pid : Ref) (mb_t : Set) : MFun t t :=
    pure (put pid {| mb_t := mb_t; mb_q := empty |}) _.
  Next Obligation.
    now rewrite H.
  Qed.

  Lemma mailbox_spawn_commute :
    forall pid1 pid2 mb_t1 mb_t2,
      pid1 <> pid2 ->
      commute (mailbox_spawn pid1 mb_t1) (mailbox_spawn pid2 mb_t2).
  Proof.
    intros pid1 pid2 mb_t1 mb_t2 Hpids s0 s2.
    unfold mailbox_spawn, pure.
    split; simpl; intros [s1 [Hs1 Hs2]].
    - exists (put pid1 {| mb_t := mb_t1; mb_q := empty |} (put pid2 {| mb_t := mb_t2; mb_q := empty |} s0)).
      split.
      + exists (put pid2 {| mb_t := mb_t2; mb_q := empty |} s0).
        sauto.
      + subst. now apply put_distict_comm.
    - exists (put pid2 {| mb_t := mb_t2; mb_q := empty |} (put pid1 {| mb_t := mb_t1; mb_q := empty |} s0)).
      split.
      + exists (put pid1 {| mb_t := mb_t1; mb_q := empty |} s0).
        sauto.
      + subst. now apply put_distict_comm.
  Qed.

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      h_setoid := s_eq_setoid;
      h_handler _ req := mailbox_step req;
      h_initial := new;
      h_spawn := mailbox_spawn;
      h_spawn_commutativity := mailbox_spawn_commute;
      h_terminate := delete_mailbox;
    |}.
End defn.
