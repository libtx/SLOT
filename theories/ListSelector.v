From Coq Require Import
  List.

Import ListNotations.

From Hammer Require Import
  Tactics.

Section defn.
  Context {A : Type}.

  Inductive Pick : list A -> A -> list A -> Prop :=
  | pick_this : forall a l,
      Pick (a :: l) a l
  | pick_next : forall a b l l',
      Pick l a l' ->
      Pick (b :: l) a (b :: l').
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
