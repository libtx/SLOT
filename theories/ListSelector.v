From Stdlib Require Import
  List.

Import ListNotations.

From Hammer Require Import
  Tactics.

Require Import Setoids Multifunction.

Open Scope slot_scope.

Section defn.
  Context {A : Type} `{Hsetoid : Setoid A}.

  Definition Pick (l : list A) a (l' : list A) : Prop :=
    Add a l' l.

  Lemma pick_equiv l1 l1' l2 a :
    l1 =p= l1' ->
    Pick l1 a l2 ->
    exists l2',
      Pick l1' a l2' /\ l2 =p= l2'.
  Proof.
    unfold Pick. intros Hl1.
    generalize dependent l2.
    induction Hl1; intros l2 Hl2.
    - exfalso. inversion Hl2.
    - sauto.
    - sauto.
    - destruct (IHHl1_1 l2 Hl2) as [l2' [Hal2' Hl2']].
      destruct (IHHl1_2 l2' Hal2') as [l2'' [Hal2'' Hl2'']].
      exists l2''. split.
      + assumption.
      + now rewrite Hl2', Hl2''.
  Qed.

  Lemma pick_two0 {a b l1 l2 l3 l2' l3'} :
    Pick l1 a l2 ->
    Pick l2 b l3 ->
    Pick l1 b l2' ->
    Pick l2' a l3' ->
    l3 =p= l3'.
  Proof.
    unfold Pick.
    intros Hl2 Hl3 Hl2' Hl3'.
    apply Permutation_cons_inv with (a := a).
    apply Permutation_cons_inv with (a := b).
    rewrite perm_swap.
    specialize (Permutation_Add Hl3) as H2p.
    specialize (Permutation_Add Hl2) as H1p.
    specialize (Permutation_Add Hl3') as H2p'.
    specialize (Permutation_Add Hl2') as H1p'.
    rewrite H2p, H1p, H2p', H1p'.
    now apply Permutation_sym.
  Qed.

  Lemma pick_two {a b l1 l2 l3} :
    Pick l1 a l2 ->
    Pick l2 b l3 ->
    exists l2' l3',
      Pick l1 b l2' /\
      Pick l2' a l3' /\
      l3' =p= l3.
  Admitted.

  Lemma pick_cons {a b l1 l2} :
    Pick (a :: l1) b l2 ->
    a <> b ->
    exists l2',
      l2 = a :: l2' /\ Pick l1 b l2'.
  Proof.
    unfold Pick.
    intros Hab H.
    generalize dependent l2.
    induction l1; intros l2 Hl2; sauto.
  Qed.

  Program Definition pick_mfun : @MFunRet A (list A) Hsetoid (setoid_permutation _) :=
    {| morphism l ret :=
        let (a, l') := ret in
        Pick l a l'
    |}.
  Next Obligation.
    eapply pick_equiv in H; eauto.
    destruct H as [l2' [Hal2' Hl2']].
    exists (a, l2'); sauto.
  Qed.

  Definition pick_cons_mfun (a : A) : @MFun (list A) (list A)
                                        (setoid_permutation _)
                                        (setoid_permutation _).
    refine (pure (cons a) _).
    intros l l' Hll'.
    now constructor.
  Defined.

  Lemma pick_cons_cons_commute (a b : A) : commute (pick_cons_mfun a) (pick_cons_mfun b).
  Proof.
    unfold pick_cons_mfun. apply pure_commutativity.
    intros l. constructor.
  Qed.
End defn.

Ltac rev_pick_cons :=
  lazymatch goal with
  | [ H : Pick (?a :: ?l1) ?b ?l2 |- _ ] =>
      let l2' := fresh l2 "'" in
      let H1 := fresh H "_l" in
      let H2 := fresh H "_r" in
      destruct (@pick_cons _ a b l1 l2 H) as [l1' [H1 H2]];
      subst
  end.

Section tests.
  Goal forall a l',
      Pick [1; 2; 3] a l' ->
        (a = 1 /\ l' = [2; 3]) \/
        (a = 2 /\ l' = [1; 3]) \/
        (a = 3 /\ l' = [1; 2]).
  Proof.
    sauto.
  Qed.
End tests.
