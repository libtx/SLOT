
Section defn.
  Context {State Arrow Result : Type}.

  Class StrictTransitionSystem := {
      ts_morph : Arrow -> relation State;
      ts_terminal : State -> Result -> Prop;
    }.

  Class TransitionSystem `{StrictTransitionSystem} := {
      ts_setoid :: Setoid State;
      ts_morph_covariance : forall (a : Arrow), rel_covariant (ts_morph a);
    }.

  Definition compose `{StrictTransitionSystem} (a b : relation State) : relation State :=
    fun s s'' =>
      exists2 s', a s s' & b s' s''.
End defn.

Notation "A '~[' B ']~>' C" := (ts_morph B A C) (at level 20) : slot_scope.
Infix "∘" := compose : slot_scope.

Section leibniz_ts.
  Context `{HSTS: StrictTransitionSystem}.

  Program Instance leibnizTS : @TransitionSystem _ _ _ HSTS | 10 := {
      ts_setoid := eq_setoid State;
    }.
  Next Obligation.
    intros s s'1 s'2 Heq H. cbn in *. subst. now exists s'2.
  Qed.
End leibniz_ts.

Open Scope slot_scope.

Section props.
  Context `{HTs: TransitionSystem}.

  Theorem ts_compose_assoc (a b c : relation State) (s s' : State) :
    (a ∘ (b ∘ c)) s s' <-> ((a ∘ b) ∘ c) s s'.
    firstorder.
  Qed.

  Lemma compose_covariance (a b : relation State) (Hcov_a : rel_covariant a) (Hcov_b : rel_covariant b) :
    rel_covariant (a ∘ b).
  Proof.
    intros s1 s2 s1'' Heq [s1' Hs1' Hs1''].
    specialize (Hcov_a s1 s2 s1' Heq Hs1').
    destruct Hcov_a as [s2' [Hs2' Heq']].
    specialize (Hcov_b s1' s2' s1'' Heq' Hs1'').
    destruct Hcov_b as [s2'' [Hs2'' Heq'']].
    exists s2''. sauto.
  Qed.

  Definition commutative (a b : relation State) : Prop :=
    forall s s',
      (a ∘ b) s s' <-> (b ∘ a) s s'.

  Definition setoid_commutative (a b : relation State) : Prop :=
    forall s s1',
      ((a ∘ b) s s1' -> exists{s2' == s1'}, (b ∘ a) s s2') /\
      ((b ∘ a) s s1' -> exists{s2' == s1'}, (a ∘ b) s s2').
End props.

Fact eq_setoid_commutative `{HST : StrictTransitionSystem} :
  forall a b,
    commutative a b <-> @setoid_commutative _ _ _ HST leibnizTS a b.
Proof.
  split; unfold commutative, setoid_commutative.
  - sauto.
  - unfold compose, exists_equiv, equiv, ts_setoid, leibnizTS, eq_setoid.
    intros H s s''. specialize (H s s'').
    sauto.
Qed.

Import ListNotations.

Section trace.
  Context `{HTS: TransitionSystem}.

  Inductive Trace : list Arrow -> State -> State -> Prop :=
  | tr_nil : forall s,
      Trace [] s s
  | tr_cons : forall s s' s'' arrow trace,
      s ~[arrow]~> s' ->
      Trace trace s' s'' ->
      Trace (arrow :: trace) s s''.

  Fixpoint trace_via_compose (t : list (relation State)) : relation State :=
    match t with
    | [] => eq
    | [a] => a
    | (a :: t) => a ∘ trace_via_compose t
    end.

  Fact trace_is_compose_fold :
    forall t s s',
      Trace t s s' <-> trace_via_compose (map ts_morph t) s s'.
  Proof with sauto.
    intros t s s''.
    split.
    - intros Ht. induction Ht.
      + easy.
      + simpl in *.
        destruct trace.
        * sauto.
        * simpl.
          exists s'.
          -- assumption.
          -- apply IHHt.
    - generalize dependent s. induction t; intros s Ht; simpl in Ht.
      + rewrite Ht. constructor.
      + destruct t; simpl in Ht.
        * constructor 2 with (s' := s'')...
        * inversion Ht.
          specialize (IHt x).
          constructor 2 with (s' := x); [assumption|].
          simpl in IHt. apply IHt in H1.
          assumption.
  Qed.

  Lemma trace_split : forall s s'' t1 t2,
      Trace (t1 ++ t2) s s''  ->
      exists s', Trace t1 s s' /\ Trace t2 s' s''.
  Proof with sauto.
    intros.
    generalize dependent s.
    induction t1; intros.
    - exists s...
    - simpl in H0. inversion H0. subst. clear H0.
      destruct (IHt1 s' H6) as [s_ [Ht1 Ht2]].
      exists s_. split; sauto.
  Qed.

  Lemma trace_concat : forall s s' s'' t1 t2,
      Trace t1 s s' ->
      Trace t2 s' s'' ->
      Trace (t1 ++ t2) s s''.
  Proof with sauto.
    intros.
    generalize dependent s.
    induction t1...
  Qed.

  Lemma trace_equiv_covariance :
    forall t, rel_covariant (Trace t).
  Proof.
    intros t.
    induction t; intros s1 s2 s1' Hs12 Hs1'.
    - inversion Hs1'. subst.
      exists s2. split.
      + constructor.
      + assumption.
    - inversion Hs1'; subst.
      eapply ts_morph_covariance in H2; eauto.
      destruct H2 as [s2_ [Hs2_ Heq]].
      specialize (IHt s' s2_ s1' Heq H5).
      destruct IHt as [s2' [Hs2' Heq']].
      exists s2'; split.
      + econstructor; eauto.
      + assumption.
  Qed.

  Lemma trace_via_compose_eqiuv_covariance :
    forall t, rel_covariant (trace_via_compose (map ts_morph t)).
  Proof.
    intros t s s1 s2 s1' Ht.
    rewrite <-trace_is_compose_fold in Ht.
    eapply trace_equiv_covariance in Ht; eauto.
    destruct Ht as [s2' [Hs2' Hs]]. exists s2'.
    rewrite <-trace_is_compose_fold. easy.
  Qed.
End trace.


Definition morph_setoid_commutative `{TransitionSystem} a b := setoid_commutative (ts_morph a) (ts_morph b).

Definition can_follow `{TransitionSystem} `{CanonicalOrder Arrow} (a b : Arrow) :=
  (canon_rel a b = true) \/ (~morph_setoid_commutative a b).


Definition TraceEnsemble {Arrow : Type} := Ensemble (list Arrow).

Section trace_equivalence.
  Context `{T : TransitionSystem} (e e' : @TraceEnsemble Arrow).

  Definition sufficient_replacement :=
    forall t s s'1, e t ->
              Trace t s s'1 ->
              exists t' s'2, e' t' /\ Trace t' s s'2 /\ s'1 == s'2.

  Definition sufficient_replacement_p :=
    forall t, e t ->
         exists t', e' t' /\ RestrictedPermutation morph_setoid_commutative t t'.

  Lemma trace_commut_swap2 a b s s'1 :
    morph_setoid_commutative a b->
    Trace [a; b] s s'1 ->
    exists{s'2 == s'1}, Trace [b; a] s s'2.
  Proof.
    intros.
    apply trace_is_compose_fold in H1. simpl in H1.
    destruct (H0 s s'1) as [Hcomm _].
    destruct (Hcomm H1) as [s'2 [H2 Hs'2]].
    exists s'2. split.
    - now rewrite trace_is_compose_fold.
    - assumption.
  Qed.

  Lemma trace_commutative_permutation s s'1 t t' :
    Trace t s s'1 ->
    RestrictedPermutation morph_setoid_commutative t t' ->
    exists{s'2 == s'1}, Trace t' s s'2.
  Proof with easy.
    intros Hls Hperm.
    generalize dependent s. generalize dependent s'1.
    induction Hperm; intros.
    - exists s. sauto.
    - inversion Hls; subst; clear Hls.
      specialize (IHHperm s'1 s' H5).
      destruct IHHperm as [s'2 [Hs'2 Hl2]].
      exists s'2; split.
      + now constructor 2 with (s' := s').
      + assumption.
    - replace (a :: b :: l) with ([a; b] ++ l) in Hls by reflexivity.
      replace (b :: a :: l) with ([b; a] ++ l) by reflexivity.
      apply trace_split in Hls. destruct Hls as [s' [Hab Hls]].
      apply trace_commut_swap2 in Hab; [|assumption].
      destruct Hab as [s_ [Hsl_ Hs_]].
      specialize (trace_equiv_covariance l s' s_ s'1 Hs_ Hls) as Hls_.
      destruct Hls_ as [s'2 [Hls_ Hs'2]].
      exists s'2. split; [|assumption].
      apply trace_concat with (s' := s_)...
    - specialize (IHHperm1 s'1 s Hls).
      destruct IHHperm1 as [s'2 [Hls'2 Hs'2]].
      specialize (IHHperm2 s'2 s Hls'2).
      destruct IHHperm2 as [s'3 [Hls'3 Hs'3]].
      exists s'3. split.
      + assumption.
      + rewrite Hs'2...
  Qed.

  (* Lemma comm_perm_sufficient_replacement : *)
  (*   sufficient_replacement_p -> *)
  (*   sufficient_replacement. *)
  (* Proof. *)
  (*   intros Hsrp t s s'1 Het Hs'1. *)
  (*   specialize (Hsrp t Het). clear Het. *)
  (*   destruct Hsrp as [t' [He't' Hperm]]. *)
  (*   generalize dependent s. generalize dependent s'1. *)
  (*   induction Hperm; intros s s'1 Ht. *)
  (*   - sauto. *)
  (*   -  *)




    -
    induction Hperm.
    - intros s s'1 He_t Hs'1.
      exists []. exists s.
      inversion Hs'1; subst.
      repeat split.
      +

    intros Hsrp t s s' Ht Hls.
    destruct (Hsrp t Ht) as [t' [Ht' Hperm]].
    induction Hperm.
    - exists []. exists s. repeat split.
      + assumption.
      + constructor.
      + inversion Hls. apply reflexivity.
    - inversion Hls; subst; clear Hls.
      assert (e l1). {

      specialize (IHHperm

    eapply trace_commutateive_permutation in Hperm; eauto.
  Qed.
End trace_equivalence.
