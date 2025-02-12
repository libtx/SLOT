From Coq Require Import
  Program
  List
  Ensembles
  Relation_Definitions
  RelationClasses
  SetoidClass
  SetoidDec.

Section exists_equiv.
  Context {S : Type} `{Setoid S}.

  Definition exists_equiv (prop : S -> Prop) (s : S) : Prop :=
    exists (s' : S), prop s' /\ s == s'.
End exists_equiv.

Notation "'exists{' A == B } , C" := (exists_equiv (fun A => C) B) (at level 300, A name, B name, C at level 300, right associativity) : type_scope.

Hint Unfold exists_equiv : slot.

Section covariant_relation.
  Context {State : Type} `{Setoid State} (R : relation State).

  Definition rel_covariant :=
    forall (s1 s2 s1' : State),
      s1 == s2 ->
      R s1 s1' ->
      exists{s2' == s1'}, R s2 s2'.
End covariant_relation.

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
    intros s1 s2 s1'' Heq Hs1''.
    destruct Hs1'' as [s1' Hs1' Hs1''].
    specialize (Hcov_a s1 s2 s1' Heq Hs1').
    destruct Hcov_a as [s2' [Hs2' Heq']].
    specialize (Hcov_b s1' s2' s1'' Heq' Hs1'').
    destruct Hcov_b as [s2'' [Hs2'' Heq'']].
    exists s2''. split.
    - econstructor; eauto.
    - assumption.
  Qed.

  Definition commutative (a b : relation State) : Prop :=
    forall s s',
      (a ∘ b) s s' <-> (b ∘ a) s s'.

  Definition setoid_commutative (a b : relation State) : Prop :=
    forall s s1',
      ((a ∘ b) s s1' -> exists{s2' == s1'}, (b ∘ a) s s2') /\
      ((b ∘ a) s s1' -> exists{s2' == s1'}, (a ∘ b) s s2').
End props.

From Hammer Require Import
  Tactics.

Theorem eq_setoid_commutative `{HST : StrictTransitionSystem} :
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

  Fixpoint trace_via_compose (t : list Arrow) : relation State :=
    match t with
    | [] => eq
    | (a :: t) => (ts_morph a) ∘ trace_via_compose t
    end.

  Lemma trace_is_compose_fold :
    forall t s s',
      Trace t s s' <-> trace_via_compose t s s'.
  Proof with easy.
    intros t s s''.
    split.
    - intros Ht. induction Ht.
      + easy.
      + simpl. unfold compose.
        exists s'...
    - generalize dependent s. induction t; intros s Ht; simpl in Ht.
      + rewrite Ht. constructor.
      + destruct Ht as [s' Hs' Hs''].
        specialize (IHt s' Hs'').
        constructor 2 with (s' := s')...
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
    forall t, rel_covariant (trace_via_compose t).
  Proof.
    intros t s s1 s2 s1' Ht.
    rewrite <-trace_is_compose_fold in Ht.
    eapply trace_equiv_covariance in Ht; eauto.
    destruct Ht as [s2' [Hs2' Hs]]. exists s2'.
    rewrite <-trace_is_compose_fold. easy.
  Qed.
End trace.
