From Coq Require Import
  List.

Import ListNotations.

From Hammer Require Import
  Tactics.

Require Import Setoids.

Open Scope slot_scope.

Section defn.
  Context {A : Type}.

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
End defn.

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
