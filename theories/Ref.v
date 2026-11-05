From Stdlib Require Import
  ZArith
  FMapInterface
  FMapAVL
  OrderedTypeEx
  Lia
  SetoidClass
  Logic.PropExtensionality.

Import ListNotations.

From Hammer Require Import
  Tactics.

From LibTx Require Import
  Classes
  Storage.Instances.AVL
  Storage.Properties.

From SLOT Require Import
  Setoids.

Definition Ref : Set := list positive.

Module RefOrd <: OrderedType.
  Module PosOT := Positive_as_OT.

  Definition t := Ref.

  Definition eq := @eq t.

  Definition eq_refl := @eq_refl t.

  Definition eq_sym := @eq_sym t.

  Definition eq_trans := @eq_trans t.

  Lemma eq_dec (a b : t) : {a = b} + {a <> b}.
  Proof.
    apply list_eq_dec, positive_eq_dec.
  Qed.

  Fixpoint eqb (a b : t) : bool :=
    match a, b with
    | [], [] =>
        true
    | _ :: _, [] =>
        false
    | [], _ :: _ =>
        false
    | a :: la, b :: lb =>
        match Pos.eqb a b with
        | true => eqb la lb
        | false => false
        end
    end.

  Lemma eqb_refl a : eqb a a = true.
  Proof.
    induction a.
    - easy.
    - simpl.
      now rewrite Pos.eqb_refl.
  Qed.

  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros.
    destruct (eq_dec a b).
    { subst. rewrite eqb_refl. now constructor. }
    { assert (H : eqb a b = false).
      2:{ rewrite H. now constructor. }
      generalize dependent b.
      induction a as [|a la].
      - sauto.
      - intros b Hb.
        destruct b as [|b lb].
        + sauto.
        + destruct (Pos.eq_dec a b) as [Hab | Hab].
          * subst. simpl. rewrite Pos.eqb_refl.
            sauto.
          * simpl.
            specialize (Pos.eqb_spec a b) as H. sauto.
    }
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

  Lemma compare_antisymm a b : compare_ a b = Gt <-> compare_ b a = Lt.
  Proof.
    split. {
      generalize dependent b.
      induction a as [|x a IH]; intros b H.
      - sauto.
      - destruct b as [|y b].
        + sauto.
        + simpl in *.
          remember (x ?= y)%positive as Hxy.
          symmetry in HeqHxy.
          destruct Hxy.
          * apply Pos.compare_eq_iff in HeqHxy. subst.
            rewrite Pos.compare_refl.
            now apply IH in H.
          * discriminate.
          * apply Pos.compare_gt_iff, POrderedType.Positive_as_OT.compare_lt_iff in HeqHxy.
            now rewrite HeqHxy.
    }
    { generalize dependent b.
      induction a as [|x a IH]; intros b H.
      - sauto.
      - destruct b as [|y b].
        + sauto.
        + simpl in *.
          remember (x ?= y)%positive as Hxy.
          symmetry in HeqHxy.
          destruct Hxy.
          * apply Pos.compare_eq_iff in HeqHxy. subst.
            rewrite Pos.compare_refl in H.
            now apply IH in H.
          * rewrite Pos.compare_lt_iff in HeqHxy. apply Pos.lt_gt,Pcompare_eq_Gt in HeqHxy.
            now rewrite HeqHxy in H.
          * reflexivity.
    }
  Qed.

  Lemma ref_compare_eq_if a b : compare_ a b = Eq -> a = b.
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

  Lemma ref_compare_eq_iff a b : compare_ a b = Eq <-> a = b.
  Proof.
    split.
    - apply ref_compare_eq_if.
    - generalize dependent b.
      induction a; intros b Hb.
      + now subst.
      + subst. simpl. rewrite Pos.compare_refl.
        now apply IHa.
  Qed.

  Lemma compare_eq_symm a b : compare_ a b = Eq -> compare_ b a = Eq.
  Proof.
    intros H.
    apply ref_compare_eq_iff in H. subst.
    now apply ref_compare_eq_iff.
  Qed.

  Definition lt a b := compare_ a b = Lt.

  Definition gt a b := compare_ a b = Gt.

  Definition ltb a b :=
    match compare_ a b with
    | Lt => true
    | _ => false
    end.

  Definition gtb a b :=
    match compare_ a b with
    | Gt => true
    | _ => false
    end.

  Lemma ref_lt_nil : forall x, ~lt x [].
  Proof.
    intros x H.
    destruct x; now cbv in H.
  Qed.

  Lemma ref_lt_append_l : forall x y z, lt (x ++ [y]) z -> lt x z.
  Proof.
    induction x.
    - sauto.
    - induction z; sauto unfold: lt, compare_.
  Qed.

  Lemma ref_lt_append_l' : forall x y z, lt x z -> lt x (z ++ [y]).
  Proof.
    intros x y z. generalize dependent x.
    induction z.
    - sauto use:ref_lt_nil.
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
      + intros z Hxy. now apply ref_lt_nil in Hxy.
      + induction z as [|c z IHz].
        * intros Hxy Hyz. now apply ref_lt_nil in Hyz.
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

  Lemma lt_append x y a b : lt x y -> lt (x ++ [a]) (y ++ [b]).
  Admitted.

  Theorem lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof.
    intros H Habsurd.
    destruct Habsurd.
    induction x; sauto use: Pos.lt_irrefl.
  Qed.

  Definition compare (a b : t) : Compare lt eq a b.
    remember (compare_ a b) as H.
    destruct H.
    - constructor 2. now apply ref_compare_eq_iff.
    - constructor 1. now symmetry in HeqH.
    - constructor 3. symmetry in HeqH. now apply compare_antisymm in HeqH.
  Qed.
End RefOrd.

Module FMap.
  Include FMapAVL.Make RefOrd.
  Include Storage.Instances.AVL.Make RefOrd.
End FMap.

From Equations Require Import
  Equations
  Signature.

Set Equations Transparent.

Module Fresh.
  Open Scope positive_scope.

  Definition t := FMap.M.t positive.

  Equations get_ (p : Ref) (cc : t) : option positive :=
    get_ p cc := get p cc.

  Equations put_ (p : Ref) (v : positive) (cc : t) : t :=
    put_ p v cc := put p v cc.

  Equations make0 (parent : Ref) (cc : t) (ctr : option positive) : Ref * t :=
    make0 parent cc (Some ctr) := (parent ++ [ctr], put parent (ctr + 1) cc);
    make0 parent cc None       := (parent ++ [1],   put parent 2         cc).

  Equations make (parent : Ref) (cc : t) : Ref * t :=
    make parent cc := make0 parent cc (get_ parent cc).

  Equations parent_of0 (ctr : positive) (acc : Ref) (l : Ref) : (Ref * positive) :=
    parent_of0 ctr acc [] := (rev' acc, ctr);
    parent_of0 ctr acc (ctr1 :: l) := parent_of0 ctr1 (ctr :: acc) l.

  Equations parent_of (ref : Ref) : option (Ref * positive) :=
    parent_of [] := None;
    parent_of (ctr :: l) := Some (parent_of0 ctr [] l).

  Section tests.
    Goal fst (make [4; 5] (FMap.M.empty positive)) = [4; 5; 1].
    Proof.
      reflexivity.
    Qed.
  End tests.

  Opaque put.
  Opaque get.

  Add Parametric Morphism (parent : Ref) : (make parent)
      with signature (equiv  ==> @equiv _ (pair_setoid' (eq_setoid _) s_eq_setoid))
      as make_morph.
  Proof.
    intros a1 a1' Hequiv.
    unfold make, make0, get_.
    rewrite <-Hequiv.
    destruct (get parent a1) as [ctr|].
    - simpl. split; [|split].
      + reflexivity.
      + intros k. rewrite Hequiv.
        reflexivity.
        exact True. (* ??? *)
    - split.
      + reflexivity.
      + rewrite Hequiv.
        * reflexivity.
        * exact True. (* ??? *)
  Qed.

  Lemma swap_make pid1 pid2 new_pid1 new_pid2 rc1 rc2 rc3 :
    pid1 <> pid2 ->
    make pid1 rc1 = (new_pid1, rc2) ->
    make pid2 rc2 = (new_pid2, rc3) ->
    exists rc2' rc3',
      rc3' == rc3 /\
      make pid2 rc1 = (new_pid2, rc2') /\
      make pid1 rc2' = (new_pid1, rc3').
  Proof.
    unfold make, get_, put_.
    intros Hpid12 Hnew1 Hnew2.
    remember (get pid1 rc1) as np1.
    remember (get pid2 rc1) as np2.
    destruct np1 as [ctr1|];
      injection Hnew1 as Hnew1 Hrc2; subst rc2;
      (* Apply distinct: *)
      lazymatch goal with
      | [ H : context [get ?p1 (put ?p2 ?ctr2 ?rc)] |- _ ] =>
          rewrite <-distinct with (k1 := p1) (k2 := p2) (v2 := ctr2) in H;
          [|assumption || now symmetry]
      end;
      destruct np2 as [ctr2|];
      rewrite <-Heqnp2 in Hnew2;
      injection Hnew2 as Hnew2 Hrc3;
      (* Create new states: *)
      lazymatch goal with
      | [ H : context [put ?pid2 ?ctr2 (put ?pid1 ?ctr1 ?rc)] |- _] =>
          exists (put pid2 ctr2 rc);
          exists (put pid1 ctr1 (put pid2 ctr2 rc));
          subst;
          split;
          [apply put_distict_comm; [assumption || now symmetry] | ]
      end;
      split; try easy;
      match goal with
      | [ H : ?p1 <> ?p2  |- context [get ?p1 (put ?p2 ?ctr2 ?rc)] ] =>
          rewrite <-distinct with (k1 := p1) (k2 := p2) (v2 := ctr2); [|assumption]
      end;
      rewrite <-Heqnp1 || rewrite <-Heqnp2;
      reflexivity.
  Qed.

  Lemma reford_app ref a :
    RefOrd.compare_ ref (ref ++ [a]) = Lt.
  Proof.
    induction ref.
    - easy.
    - simpl.
      now rewrite Pos.compare_refl.
  Qed.

  Lemma child_gt_parent parent child cc cc' :
    (child, cc') = make parent cc ->
    RefOrd.compare_ parent child = Lt.
  Proof.
    intros Hmake.
    funelim (make parent cc).
    rewrite <-Heqcall in Hmake.
    funelim (make0 parent cc (get_ parent cc));
      rewrite <-Heqcall0 in Hmake;
      inversion Hmake;
      subst;
      apply reford_app.
  Qed.

  Lemma gt_parents_children {cc1 cc2 cc1' cc2'} p1 p2 new1 new2 :
    RefOrd.gt p1 p2 ->
    (new1, cc1') = make p1 cc1 ->
    (new2, cc2') = make p2 cc2 ->
    RefOrd.gt new1 new2.
  Proof.
    intros Hp.
    assert (Hslv : forall a b, RefOrd.gt (p1 ++ [a]) (p2 ++ [b])). {
      intros a b.
      apply RefOrd.compare_antisymm.
      apply RefOrd.compare_antisymm in Hp.
      apply (RefOrd.lt_append p2 p1 b a Hp).
    }
    unfold make, make0.
    intros H1 H2.
    destruct (get_ p1 cc1); destruct (get_ p2 cc2);
      injection H1 as H1new Hcc1'; injection H2 as H2new Hcc2';
      subst;
      apply Hslv.
  Qed.

  Lemma different_parents_children {cc1 cc2 cc1' cc2'} p1 p2 new1 new2 :
    p1 <> p2 ->
    (new1, cc1') = make p1 cc1 ->
    (new2, cc2') = make p2 cc2 ->
    new1 <> new2.
  Proof.
    intros Hp.
    assert (Hslv : forall a b, p1 ++ [a] <> p2 ++ [b]). {
      intros a b Habsurd.
      apply app_inj_tail_iff in Habsurd.
      firstorder.
    }
    unfold make, make0.
    intros H1 H2.
    destruct (get_ p1 cc1); destruct (get_ p2 cc2);
      injection H1 as H1new Hcc1'; injection H2 as H2new Hcc2';
      subst;
      apply Hslv.
  Qed.
End Fresh.
