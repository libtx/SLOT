From SLOT Require Import
  Trace.

From Coq Require Import
  List
  ZArith.
Import ListNotations.

Open Scope positive_scope.

Inductive Command := | foo | bar.

Inductive Label :=
| spawn : positive -> Label
| cmd : positive -> Command -> Label.

Record State :=
  { id : positive;
    commands : list Command;
  }.

Inductive State' : State -> @Future State Label True -> Prop :=
| State'₀ : forall i,
    State' {| id := i; commands := [] |}~>[]
| State'₁ : forall i c cmds,
    State' {| id := i; commands := c :: cmds |} ~[cmd i c]~>
           {| id := i; commands := cmds |}.

Instance tsState : TransitionSystem State Label True := { future := State' }.

From Hammer Require Import
  Tactics.

Ltac inv a := inversion a; subst; clear a.

Section sys1.
  Let sys1 := Σ₁ {| id := 1; commands := [] |} (spawn 1) Σø.

  Goal forall (t : list Label),
      Trace _ sys1 Σø t ->
      t = [spawn 1].
  Proof.
    intros.
    inv H. simpl in *. inv H0.
    - inv H2. apply Σø' in H1. destruct H1. now rewrite H.
    - inv H2.
    - inv H2.
  Qed.
End sys1.

Section sys2.
  Let sys2 := Σ₁ {| id := 1; commands := [foo] |} (spawn 1) Σø.

  Goal forall (t : list Label),
      Trace _ sys2 Σø t ->
      t = [spawn 1; cmd 1 foo].
  Proof.
    intros. subst sys2.
    inv H. cbv in *. inv H0.
    - exfalso. inv H2.
    - inv H2. inv H1. inv H.
      + apply Σø' in H0. destruct H0. now rewrite H.
      + exfalso. inv H2.
      + inv H2.
    - inv H2.
  Qed.
End sys2.

Section sys3.
  Let sys3 := Σ₁ {| id := 1; commands := [] |} (spawn 1)
                (Σ₁ {| id := 2; commands := [] |} (spawn 2) Σø).

  Goal forall (t : list Label),
      Trace _ sys3 Σø t ->
      t = [spawn 1; spawn 2] \/ t = [spawn 2; spawn 1].
  Proof.
    intros.
    inv H. cbv in *. inv H0.
    - simpl in H2. clear H2. inv H1. inv H.
      + left. inv H0.
        * reflexivity.
        * inv H.
      + exfalso. inv H0. inv H; inv H2.
      + exfalso. inv H2.
    - exfalso. inv H2.
    - inv H1. inv H0.
      + inv H. inv H1. inv H2. now right.
      + exfalso. clear H3. inv H2.
        * inv H.
          -- inv H1.
          -- simpl in H2. inv H2.
          -- inv H3. inv H2.
        * inv H3.
        * inv H3.
  Qed.
End sys3.
