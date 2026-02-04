From Coq Require Export
  SetoidClass.

From Coq Require Import
  Program.

From Hammer Require Import
  Tactics.

Section setoid_pair.
  Context (A B : Type) `{Setoid A} `{Setoid B}.

  Program Instance setoidPair : Setoid (A * B) :=
    {| equiv (a b : (A * B)) :=
        let (a_l, a_r) := a in
        let (b_l, b_r) := b in
        equiv a_l b_l /\ equiv a_r b_r;
    |}.
  Solve All Obligations with sauto unfold:Reflexive,Symmetric,Transitive.
End setoid_pair.

Section setoid_option.
  Context (T : Type) `{Setoid T}.

  Program Instance setoid_option : Setoid (option T) :=
    {| equiv (a b : option T) :=
        match a, b with
        | Some a, Some b => equiv a b
        | None, None => True
        | _, _ => False
        end;
    |}.
  Solve All Obligations with sauto unfold:Reflexive,Symmetric,Transitive.
End setoid_option.
