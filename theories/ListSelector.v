From Coq Require Import
  List.
Import ListNotations.

Section defn.
  Context {A : Type}.

  Inductive Pick : list A -> (A * list A) -> Prop :=
  | pick_this : forall a l,
      Pick (a :: l) (a, l)
  | pick_next : forall a b l l',
      Pick l (a, l') ->
      Pick (b :: l) (a, b :: l').
End defn.

Section tests.
  Goal forall a,
      Pick [1; 2] a ->
      a = (1, [2]) \/ a = (2, [1]).
  Proof.
    intros a H.
    inversion_clear H.
    - now left.
    - inversion_clear H0.
      + now right.
      + inversion H.
  Qed.
End tests.
