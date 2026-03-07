From Coq Require Export
  SetoidClass
  Permutation.

From Coq Require Import
  Program.

From Hammer Require Import
  Tactics.

From LibTx Require Import
  Storage.

Section pair.
  Context (A B : Type) `{Setoid A} `{Setoid B}.

  Global Program Instance pair_setoid : Setoid (A * B) :=
    {| equiv (a b : (A * B)) :=
        let (a_l, a_r) := a in
        let (b_l, b_r) := b in
        equiv a_l b_l /\ equiv a_r b_r;
    |}.
  Solve All Obligations with sauto unfold:Reflexive,Symmetric,Transitive.
End pair.

Definition pair_setoid' {A B : Type} (a : Setoid A) (b : Setoid B) :=
  @pair_setoid A B a b.

Section option.
  Context (T : Type) `{Setoid T}.

  Global Program Instance setoid_option : Setoid (option T) :=
    {| equiv (a b : option T) :=
        match a, b with
        | Some a, Some b => equiv a b
        | None, None => True
        | _, _ => False
        end;
    |}.
  Solve All Obligations with sauto unfold:Reflexive,Symmetric,Transitive.
End option.

Section permutation.
  Context (T : Type).

  Global Program Instance setoid_permutation : Setoid (list T) | 10 :=
    {| equiv a b := Permutation a b |}.
End permutation.

Infix "=p=" := (@equiv _ (setoid_permutation _)) (at level 50) : slot_scope.
Infix "=s=" := (@equiv _ s_eq_setoid) (at level 50) : slot_scope.
