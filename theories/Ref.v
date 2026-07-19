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

  Lemma compare_asymm a b : compare_ a b = Gt -> compare_ b a = Lt.
  Proof.
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
  Qed.

  Lemma ref_compare_eq_iff a b : compare_ a b = Eq -> a = b.
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
    - constructor 3. symmetry in HeqH. now apply compare_asymm in HeqH.
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
    make0 parent cc (Some ctr) := (ctr :: parent, put parent (ctr + 1) cc);
    make0 parent cc None       := (1   :: parent, put parent 2         cc).

  Equations make  (parent : Ref) (cc : t) : Ref * t :=
    make parent cc := make0 parent cc (get_ parent cc).

  Definition is_valid_ref (ref : Ref) (cc : t) : bool :=
    match ref with
    | [] => true
    | (child :: parent) =>
        match get parent cc with
        | None =>
            false
        | Some parent_child_ctr =>
            Pos.ltb child parent_child_ctr
        end
    end.

  Opaque put.
  Opaque get.

  Lemma makes_valid_ref (parent new : Ref) (cc cc' : t) :
    make parent cc = (new, cc') ->
    is_valid_ref new cc' = true.
  Proof with try easy; lia.
    unfold make, is_valid_ref, get_.
    intros Hnew.
    destruct (get parent cc).
    - inversion Hnew.
      rewrite keep.
      assert (H : p <= p + 1) by lia.
      destruct (Pos.ltb_spec0 p (p + 1))...
    - inversion Hnew.
      rewrite keep.
      destruct (Pos.leb_spec0 1 2)...
  Qed.

  Lemma make_keeps_valid (parent other new : Ref) (cc cc' : t) :
    is_valid_ref other cc = true ->
    make parent cc = (new, cc') ->
    is_valid_ref other cc' = true.
  Proof.
    unfold make, is_valid_ref, get_.
    intros Hvalid Hnew.
    destruct other as [|oc oparent].
    - easy.
    - destruct (RefOrd.eq_dec oparent parent).
      2:{ (* parent <> oparent *)
        destruct (get parent cc);
          inversion Hnew; clear Hnew;
          rewrite <-distinct; assumption.
      }
      (* parent = oparent *)
      subst. unfold Ref in *.
      destruct (get parent cc); inversion Hnew; clear Hnew.
      + subst. rewrite keep.
        destruct (Pos.ltb_spec0 oc (p + 1));
          destruct (Pos.ltb_spec0 oc p);
          try easy; lia.
      + discriminate.
  Qed.

  Lemma make_valid_not_equal (parent other new : Ref) (cc cc' : t) :
    is_valid_ref other cc = true ->
    make parent cc = (new, cc') ->
    new <> other.
  Proof.
    unfold is_valid_ref, make, get_.
    intros Hvalid Hnew.
    destruct other as [|oc oparent].
    - unfold make0 in Hnew. sauto.
    - destruct (RefOrd.eq_dec parent oparent).
      2:{ (* parent <> oparent *)
        destruct (get parent cc) as [pctr|];
          inversion Hnew; clear Hnew; sauto.
      }
      (* parent = oparent *)
      intros Habsurd.
      subst.
      unfold Ref in *.
      remember (get oparent cc) as maybe_ctr.
      destruct maybe_ctr as [ctr|].
      + inversion Hnew; clear Hnew.
        subst.
        destruct (Pos.ltb_spec0 oc oc); lia.
      + discriminate.
  Qed.

  Lemma is_valid_neq_proxy a b rc :
    is_valid_ref a rc = true ->
    is_valid_ref b rc = false ->
    a <> b.
  Proof.
    unfold Fresh.is_valid_ref.
    intros Ha Hb.
    destruct a as [|a_h a_t]; destruct b as [|b_h b_t]; intros H.
    - discriminate.
    - inversion H.
    - inversion H.
    - injection H as H_h H_t. subst. now rewrite Ha in Hb.
  Qed.

  Lemma is_valid_equiv ref cc cc' :
    s_eq cc cc' ->
    is_valid_ref ref cc = true ->
    is_valid_ref ref cc' = true.
  Proof.
    unfold is_valid_ref.
    intros Hequiv Hvalid.
    destruct ref.
    - easy.
    - now rewrite <-Hequiv.
  Qed.

  Add Parametric Morphism (parent : Ref) :
    (make parent) with signature (equiv  ==> @equiv _ (pair_setoid' (eq_setoid _) s_eq_setoid)) as make_morph.
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

  Inductive NewValidRef (parent : Ref) (cc : Fresh.t) : Type :=
  | new_valid_ref : forall (new : Ref) (cc' : Fresh.t),
      is_valid_ref new cc' = true ->
      make parent cc = (new, cc') ->
      NewValidRef parent cc.

  Program Equations make_valid p c: NewValidRef p c :=
    make_valid p c with get__equation_1 p c, get_ p c => {
      make_valid p c H (Some ctr) := new_valid_ref p c (ctr :: p) (put_ p (ctr + 1) c) _ _;
      make_valid p c H None := new_valid_ref p c (1 :: p) (put_ p 2 c) _ _;
    }.
  Next Obligation.
    unfold put_. rewrite keep.
    assert (H1 : ctr <= ctr + 1) by lia.
    destruct (Pos.ltb_spec0 ctr (ctr + 1)); lia.
  Qed.
  Next Obligation.
    now rewrite make_equation_1, <- make0_equation_1, H.
  Qed.
  Next Obligation.
    unfold put_. rewrite keep.
    assert (H1 : 1 <= 2) by lia.
    destruct (Pos.ltb_spec0 1 2); lia.
  Qed.
  Next Obligation.
    now rewrite make_equation_1, <- make0_equation_2, H.
  Qed.

  Check makes_valid_ref.

  Lemma make_valid_eq parent cc new cc' (H : make parent cc = (new, cc')) :
    make_valid parent cc = new_valid_ref parent cc new cc' (makes_valid_ref parent new cc cc' H) H.
  Proof.
    funelim (make_valid parent cc).
    - assert (H1 : ctr :: p = new /\ put_ p (ctr + 1) c = cc'). {
        clear Heq0 Heqcall.
        funelim (make p c).
        rewrite Heq in Heqcall. symmetry in H0. rewrite <-H0 in Heqcall.
        unfold make0 in Heqcall.
        apply pair_equal_spec in Heqcall.
        funelim (put_ parent (ctr + 1) cc). now rewrite Heqcall0 in Heqcall.
      }
      destruct H1 as [Hnew Ncc']. subst.
      replace (make_valid_obligations_obligation_2 p c ctr H) with H0 by apply proof_irrelevance.
      now replace (make_valid_obligations_obligation_1 p c ctr) with (makes_valid_ref p (ctr :: p) c (put_ p (ctr + 1) c) H0) by apply proof_irrelevance.
    - assert (H1 : 1 :: p = new /\ put_ p 2 c = cc'). {
        clear Heq0 Heqcall.
        funelim (make p c).
        rewrite Heq in Heqcall. symmetry in H0. rewrite <-H0 in Heqcall.
        unfold make0 in Heqcall.
        apply pair_equal_spec in Heqcall.
        funelim (put_ parent 2 cc). now rewrite Heqcall0 in Heqcall.
      }
      destruct H1 as [Hnew Ncc']. subst.
      replace (make_valid_obligations_obligation_4 p c H) with H0 by apply proof_irrelevance.
      now replace (make_valid_obligations_obligation_3 p c) with (makes_valid_ref p (1 :: p) c (put_ p 2 c) H0) by apply proof_irrelevance.
  Qed.
End Fresh.

Opaque Fresh.make_valid.
