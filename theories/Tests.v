From Stdlib Require Import
  List
  ZArith
  SetoidClass
  SetoidDec
  Decidable.
Import ListNotations.

From SLOT Require Import
  Setoids
  TokenMachine
  TransitionSystem
  Ref
  ListSelector
  IOHandler
  RestrictedPermutation
  Tactics.

From Hammer Require Import
  Tactics.

From Ltac2 Require
  Fresh
  String
  Ident
  Std
  Ident
  Constr
  Control.

Set Default Proof Mode "Ltac2".

Section ts_test.
  Record state : Set := mkS {a : nat; b : nat}.

  Inductive PairEvent : Set := l | r.

  Let ret_t := @ts_ret state PairEvent.

  Inductive pair_ts_morph : state -> ret_t -> Prop :=
  | m_none : pair_ts_morph (mkS 0 0) None
  | m_left : forall a b,
      pair_ts_morph (mkS (S a) b) (Some (l, mkS a b))
  | m_right : forall a b,
      pair_ts_morph (mkS a (S b)) (Some (r, mkS a b)).

  Program Definition pair_mfun : MFun state ret_t :=
    {| morphism := pair_ts_morph |}.
  Next Obligation.
    now exists y.
  Qed.

  Let canon_rel a b :=
        match a, b with
        | l, r => False
        | _, _ => True
        end.

  Lemma canon_rel_dec_ a b : decidable (canon_rel a b).
    sauto.
  Qed.

  Lemma canon_rel_total_ a b : canon_rel a b \/ canon_rel b a.
    sauto.
  Qed.

  Instance canon_rel_C : CanonicalOrder canon_rel :=
    {| canon_rel_dec := canon_rel_dec_;
       canon_rel_total := canon_rel_total_;
    |}.

  Instance tsPair : @TransitionSystem state PairEvent :=
    {|
      ts_setoid := eq_setoid _;
      ts_canon_rel := canon_rel;
      ts_canon_order := canon_rel_C;
      ts_state_trans := pair_mfun;
    |}.

  Lemma pair_commute : ts_event_commute l r.
  Proof.
    intros a c. split; intros H;
      destruct H as [b H];
      exists c; sauto.
  Qed.

  Goal forall l s_e,
      TSMFunGen (mkS 0 0) l s_e ->
      l = [] /\ s_e = (mkS 0 0).
  Proof.
    sauto.
  Qed.

  Let s_end := mkS 0 0.

  (* Generator always goes to the end; doesn't abort: *)
  Goal ~TSMFunGen (mkS 1 1) [] (mkS 1 1).
    sauto.
  Qed.

  Goal forall tr, TSMFunGen (mkS 1 0) tr s_end ->
             tr = [l].
    sauto.
  Qed.

  Goal forall tr, TSMFunGen (mkS 1 1) tr s_end ->
             tr = [l; r] \/ tr = [r; l].
    sauto.
  Qed.

  Goal forall tr, TSMFunGen (mkS 1 1) tr s_end ->
             CanonicalTrace tr (mkS 1 1) s_end ->
             tr = [r; l].
  Proof.
    intros tr H Hcanon.
    ts_step H.
    inversion Hs; subst.
    - ts_step H.
      inversion Hs0; subst.
      + exfalso.
        inversion Hcanon; subst.
        simpl in H3. unfold can_follow in H3.
        assert (Hlr : ~tm_canon_rel l r) by sauto.
        apply Hlr in H3.
        * assumption.
        * apply pair_commute.
    - ts_step H.
      inversion Hs0; subst.
      ts_step H.
      + reflexivity.
      + inversion Hs1.
  Qed.
End ts_test.
