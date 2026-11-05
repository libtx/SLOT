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
  Proof.
    intros Hab Hsend.
    revert Hab.
    induction Hsend.
    intros H.
    exists (put pid {| mb_t := T; mb_q := push msg mbox |} b).
    split.
    - apply do_send_msg_.
    - now rewrite H.
  Qed.

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

  (* begin details *)
  Lemma delete_mailbox_morph (normal : bool) (pid : Ref) s s' :
    morphism (delete_mailbox normal pid) s s' <-> @delete _ Mailbox _ _ pid s = s'.
  Proof.
    split; intro H; exact H.
  Qed.
  (* end details *)

  Opaque put.
  Opaque delete.

  Program Definition mailbox_spawn (pid : Ref) (mb_t : Set) : MFun t t :=
    pure (put pid {| mb_t := mb_t; mb_q := empty |}) _.
  Next Obligation.
    now rewrite H.
  Qed.

  Lemma delete_put_comm (s : t) (v : Mailbox) k1 k2 :
      k1 <> k2 ->
      delete k1 (put k2 v s) == put k2 v (delete k1 s).
  Proof.
    intros Hk12.
    constructor. intros k.
    destruct (RefOrd.eq_dec k k1) as [Hk|Hk].
    - subst k.
      rewrite delete_keep.
      rewrite <- (distinct (delete k1 s) k1 k2 v Hk12).
      rewrite delete_keep.
      reflexivity.
    - destruct (RefOrd.eq_dec k k2) as [Hk2|Hk2].
      + subst k.
        rewrite <- (delete_distinct (put k2 v s) k2 k1 (not_eq_sym Hk12)).
        rewrite keep, keep.
        reflexivity.
      + rewrite <- (delete_distinct (put k2 v s) k k1 Hk).
        rewrite <- (distinct s k k2 v Hk2).
        rewrite <- (distinct (delete k1 s) k k2 v Hk2).
        rewrite <- (delete_distinct s k k1 Hk).
        reflexivity.
  Qed.

  Program Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      h_setoid := s_eq_setoid;
      h_perform_io _ req := mailbox_step req;
      h_initial := new;
      h_spawn := mailbox_spawn;
      h_terminate := delete_mailbox;
    |}.
  Next Obligation.
    rename x into mb0.
    rename y into mb2.
    destruct H0 as [mb1 [Hmb1 Hmb2]].
    simpl in *.
    rewrite <-Hmb1 in Hmb2.
    specialize (put_distict_comm mb0 pid1 pid2
                                 {| mb_t := mb_t1; mb_q := empty |}
                                 {| mb_t := mb_t2; mb_q := empty |}
                                 H) as Hcomm.
    exists (put pid1 {| mb_t := mb_t1; mb_q := empty |} (put pid2 {| mb_t := mb_t2; mb_q := empty |} mb0)).
    split.
    - exists (put pid2 {| mb_t := mb_t2; mb_q := empty |} mb0).
      now split.
    - now subst.
  Qed.
End defn.
