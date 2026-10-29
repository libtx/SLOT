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

  Instance mailboxHandler : @IOHandler MBReq MBRet :=
    {|
      h_state := t;
      h_setoid := s_eq_setoid;
      h_handler := fun _ _ _ req => mailbox_step req;
      h_initial := new;
      h_spawn := mailbox_spawn;
      h_spawn_commutativity := mailbox_spawn_commute;
      h_terminate := delete_mailbox;
      h_handler_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_spawn_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_terminate_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
    |}.
End defn.
