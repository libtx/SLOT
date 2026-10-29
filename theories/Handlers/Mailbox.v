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

  Definition delete_mailbox (_normal : bool) (pid : Ref) (_rc : Fresh.t)
    (_pid_valid : is_valid_pid pid _rc) : MFun t t.
    set (f := @delete _ Mailbox _ _ pid).
    refine (pure f _).
    - intros s s' H.
      rewrite H; easy.
  Defined.

  (* begin details *)
  Lemma delete_mailbox_morph (normal : bool) (pid : Ref) (rc : Fresh.t)
      (v : is_valid_pid pid rc) s s' :
    morphism (delete_mailbox normal pid rc v) s s' <-> @delete _ Mailbox _ _ pid s = s'.
  Proof.
    split; intro H; exact H.
  Qed.
  (* end details *)

  Opaque put.

  Program Definition mailbox_spawn (pid : Ref) (_rc : Fresh.t)
    (_pid_fresh : is_invalid_pid pid _rc) (mb_t : Set) : MFun t t :=
    pure (put pid {| mb_t := mb_t; mb_q := empty |}) _.
  Next Obligation.
    now rewrite H.
  Qed.

  Lemma mailbox_spawn_commute :
    forall pid1 pid2 mb_t1 mb_t2
           (rc1 : Fresh.t) (fresh1 : is_invalid_pid pid1 rc1)
           (rc2 : Fresh.t) (fresh2 : is_invalid_pid pid2 rc2),
      pid1 <> pid2 ->
      forall s0 s1 s2,
        s0 ~[mailbox_spawn pid1 rc1 fresh1 mb_t1]~> s1 ->
        s1 ~[mailbox_spawn pid2 rc2 fresh2 mb_t2]~> s2 ->
        forall (rc2' : Fresh.t) (fresh2' : is_invalid_pid pid2 rc2')
               (rc1' : Fresh.t) (fresh1' : is_invalid_pid pid1 rc1'),
        exists{s2' == s2}, exists s1',
          s0 ~[mailbox_spawn pid2 rc2' fresh2' mb_t2]~> s1' /\
          s1' ~[mailbox_spawn pid1 rc1' fresh1' mb_t1]~> s2'.
  Proof.
    intros pid1 pid2 mb_t1 mb_t2 rc1 f1 rc2 f2 Hpids s0 s1 s2 H1 H2 rc2' f2' rc1' f1'.
    unfold mailbox_spawn, pure in *.
    cbn in H1, H2.
    subst s1. subst s2.
    exists (put pid1 {| mb_t := mb_t1; mb_q := empty |}
              (put pid2 {| mb_t := mb_t2; mb_q := empty |} s0)).
    split.
    - exists (put pid2 {| mb_t := mb_t2; mb_q := empty |} s0).
      split; reflexivity.
    - now apply put_distict_comm.
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

  Lemma mailbox_spawn_terminate_commute :
    forall (normal : bool) (pid1 pid2 : Ref) (mb_t : Set) (rc : Fresh.t)
           (valid1 : is_valid_pid pid1 rc) (fresh2 : is_invalid_pid pid2 rc),
      commute (delete_mailbox normal pid1 rc valid1)
              (mailbox_spawn pid2 rc fresh2 mb_t).
  Proof.
    intros normal pid1 pid2 mb_t rc valid1 fresh2.
    assert (Hne : pid1 <> pid2)
      by (apply (Fresh.is_valid_neq_proxy pid1 pid2 rc); assumption).
    unfold commute, commute_def, exists_equiv.
    intros s0 s2.
    split.
    - (* terminate, then spawn *)
      intros Hrun.
      destruct Hrun as [s1 [H1 H2]].
      rewrite delete_mailbox_morph in H1.
      unfold mailbox_spawn, pure in H2.
      cbn in H2.
      subst.
      exists (delete pid1 (put pid2 {| mb_t := mb_t; mb_q := empty |} s0)).
      split.
      + exists (put pid2 {| mb_t := mb_t; mb_q := empty |} s0).
        split; reflexivity.
      + symmetry. apply delete_put_comm. exact Hne.
    - (* spawn, then terminate *)
      intros Hrun.
      destruct Hrun as [s1 [H1 H2]].
      unfold mailbox_spawn, pure in H1.
      cbn in H1.
      rewrite delete_mailbox_morph in H2.
      subst.
      exists (put pid2 {| mb_t := mb_t; mb_q := empty |} (delete pid1 s0)).
      split.
      + exists (delete pid1 s0).
        split; reflexivity.
      + apply delete_put_comm. exact Hne.
  Qed.

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      h_setoid := s_eq_setoid;
      h_perform_io _ _ _ req := mailbox_step req;
      h_initial := new;
      h_spawn := mailbox_spawn;
      h_spawn_commutativity := mailbox_spawn_commute;
      h_terminate := delete_mailbox;
      h_perform_io_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_spawn_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_terminate_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_spawn_terminate_commutativity := mailbox_spawn_terminate_commute;
    |}.
End defn.
