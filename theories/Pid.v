From Coq Require Import
  ZArith
  FMapInterface
  FMapAVL
  OrderedTypeEx.

Import ListNotations.

From Hammer Require Import
  Tactics.

From LibTx Require
  Storage.Instances.AVL.

Definition PID : Set := list positive.

Module PIDOrd <: OrderedType.
  Module PosOT := Positive_as_OT.

  Definition t := PID.

  Definition eq := @eq t.

  Definition eq_refl := @eq_refl t.

  Definition eq_sym := @eq_sym t.

  Definition eq_trans := @eq_trans t.

  Lemma eq_dec (a b : t) : {a = b} + {a <> b}.
  Proof.
    apply list_eq_dec, positive_eq_dec.
  Qed.

  Fixpoint compare_ (a b : t) : comparison :=
    match a, b with
    | [], [] => Eq
    | [], _ => Lt
    | _, [] => Gt
    | a :: l1, b :: l2 =>
        match (a ?= b)%positive with
        | Eq => compare_ l1 l2
        | o => o
        end
    end.

  Lemma compare_asymm a b : compare_ a b = Gt -> compare_ b a = Lt.
  Proof.
    generalize dependent b.
    induction a as [|x a IH]; intros b H.
    - sauto.
    - destruct b as [|y b].
      + sauto.
      + simpl in *.
        remember (x ?= y)%positive as Hxy.
        destruct Hxy.
        * symmetry in HeqHxy. apply Pos.compare_eq_iff in HeqHxy. subst.
  Admitted.

  Lemma pid_compare_eq_iff a b : compare_ a b = Eq -> a = b.
  Proof.
    unfold compare_.
    generalize dependent b.
    induction a as [|x a IH].
    - intros b H. now destruct b.
    - intros b H.
      destruct b as [|y b].
      + discriminate.
      + remember (x ?= y)%positive as Hxy.
        destruct Hxy.
        * symmetry in HeqHxy. apply Pos.compare_eq_iff in HeqHxy.
          apply IH in H.
          now subst.
        * discriminate.
        * discriminate.
  Qed.

  Definition lt a b := compare_ a b = Lt.

  Lemma pid_lt_nil : forall x, ~lt x [].
  Proof.
    intros x H.
    destruct x; now cbv in H.
  Qed.

  Lemma pid_lt_append_l : forall x y z, lt (x ++ [y]) z -> lt x z.
  Proof.
    induction x.
    - sauto.
    - induction z; sauto unfold: lt, compare_.
  Qed.

  Lemma pid_lt_append_l' : forall x y z, lt x z -> lt x (z ++ [y]).
  Proof.
    intros x y z. generalize dependent x.
    induction z.
    - sauto use:pid_lt_nil.
    - induction x; sauto unfold: lt, compare_.
  Qed.

  Lemma lt_app_case : forall a b x y, lt (a :: x) (b :: y) ->
                                 (a = b /\ lt x y) \/ (Pos.lt a b).
  Proof.
    unfold lt, compare_.
    simpl. intros.
    remember ((a ?= b)%positive) as Hab.
    destruct Hab.
    - symmetry in HeqHab. apply Pos.compare_eq_iff in HeqHab. subst.
      left. split; easy.
    - right. symmetry in HeqHab. now rewrite Pos.compare_lt_iff in HeqHab.
    - discriminate.
  Qed.

  Lemma lt_app_same : forall a x y, lt x y -> lt (a :: x) (a :: y).
  Proof.
    intros.
    unfold lt, compare_.
    now rewrite Pos.compare_refl.
  Qed.

  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    induction x as [|a x IHx].
    - sauto.
    - destruct y as [|b y].
      + intros z Hxy. now apply pid_lt_nil in Hxy.
      + induction z as [|c z IHz].
        * intros Hxy Hyz. now apply pid_lt_nil in Hyz.
        * intros Hxy Hyz.
          specialize (IHz Hxy).
          apply lt_app_case in Hxy. apply lt_app_case in Hyz.
          destruct Hxy as [[Hab Hxy] | Hxy], Hyz as [[Hbc Hyz] | Hyz]; subst.
          -- apply lt_app_same, (IHx y z Hxy Hyz).
          -- sauto unfold:lt.
          -- sauto unfold:lt.
          -- specialize (Positive_as_OT.lt_trans _ _ _ Hxy Hyz) as H.
             sauto unfold:lt.
  Qed.

  Theorem lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof.
    intros H Habsurd.
    destruct Habsurd.
    induction x; sauto use: Pos.lt_irrefl.
  Qed.

  Definition compare (a b : t) : Compare lt eq a b.
    remember (compare_ a b) as H.
    destruct H.
    - constructor 2. now apply pid_compare_eq_iff.
    - constructor 1. now symmetry in HeqH.
    - constructor 3. symmetry in HeqH. now apply compare_asymm in HeqH.
  Qed.
End PIDOrd.

Module FMap.
  Include FMapAVL.Make PIDOrd.
  Include Storage.Instances.AVL.Make PIDOrd.
End FMap.
