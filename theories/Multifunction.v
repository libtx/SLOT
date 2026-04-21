(** * Multi-valued functions
 *)
From Stdlib Require Import
  Program
  List
  Relation_Definitions
  RelationClasses
  SetoidClass
  SetoidDec
  Classes.Morphisms.

From Hammer Require Import
  Tactics.

From SLOT Require Import
  Setoids
  RestrictedPermutation.

Import ListNotations.

(** Existential covariance wrt. setoid *)
Section exists_equiv.
  Context {S : Type} `{Setoid S}.

  Definition exists_equiv (prop : S -> Prop) (s : S) : Prop :=
    exists (s' : S), prop s' /\ s == s'.
End exists_equiv.

Notation "'exists{' A == B } , C" :=
  (exists_equiv (fun A => C) B)
  (at level 300, A name, B name, C at level 300, right associativity) : type_scope.

Hint Unfold exists_equiv : slot.

(** Definition of a multi-valued function *)
Section mfun.
  Context (Dom Cod : Type) `{Setoid Dom} `{Setoid Cod}.

  Structure MFun : Type := {
      morphism : Dom -> Cod -> Prop;
      morphism_covariance : forall x x' y,
        x == x' ->
        morphism x y ->
        exists{y' == y}, morphism x' y';
    }.
End mfun.

(* begin details *)
Global Arguments morphism {_ _ _ _}.
Global Arguments morphism_covariance {_ _ _ _}.
(* end details *)

Declare Scope slot_scope.
Open Scope slot_scope.

Notation "A '~[' B ']~>' C" := (morphism B A C) (at level 20) : slot_scope.
Notation "C '<~[' B ']~' A" := (morphism B A C) (at level 20) : slot_scope.

(* begin details *)
Ltac morph_shift morphism point :=
  lazymatch goal with
  | [Hequiv : point == ?A, Hmorph : ?A ~[morphism]~> ?B |- _] =>
      (* FIXME: ideally we should not modify the original hypothesis *)
      symmetry in Hequiv; morph_shift morphism point
  | [Hequiv : ?A == point, Hmorph : ?A ~[morphism]~> ?B |- _] =>
      let B' := fresh B "'" in
      let Hequiv' := fresh "Hequiv_" B "_" B' in
      let Hmorph' := fresh "Hmorph_" point "_" B' in
      destruct (morphism_covariance _ _ _ _ Hequiv Hmorph) as [B' [Hmorph' Hequiv']]
  end.
(* end details *)

(** Composition of multi-valued functions *)
Section compose.
  Context {A B C : Type} `{HA : Setoid A} `{HB : Setoid B} `{HC : Setoid C}.

  Let F := @MFun A B HA HB.
  Let G := @MFun B C HB HC.

  Program Definition compose (f : F) (g : G) : MFun A C :=
    {|
      morphism x z :=
        exists y, morphism f x y /\ morphism g y z;
    |}.
  Next Obligation.
    rename y into z. rename H0 into y.
    morph_shift f x'.
    morph_shift g y'.
    exists z'. sauto.
  Qed.
End compose.

Notation "g ∘ f" := (compose f g) : slot_scope.

Section assoc.
  Context {A B C D} `{HA : Setoid A} `{HB : Setoid B} `{HC : Setoid C} `{HD : Setoid D}.

  Let F := @MFun A B HA HB.
  Let G := @MFun B C HB HC.
  Let H := @MFun C D HC HD.

  Lemma mfun_assoc (f : F) (g : G) (h : H) :
    forall a b,
      a ~[h ∘ (g ∘ f)]~> b <-> a ~[(h ∘ g) ∘ f]~> b.
  Proof.
    sauto.
  Qed.
End assoc.

Section props.
  Context {A : Type} `{Hsetoid : Setoid A}.
  Let T := @MFun A A Hsetoid Hsetoid.

  (** Strong definition of commutativity based on equality *)
  Definition eq_commute (f g : T) :=
    forall (x y : A), x ~[g ∘ f]~> y <-> x ~[f ∘ g]~> y.

  (** Relaxed version of the above based on equivalence *)
  Definition commute (f g : T) :=
    forall x y,
      (x ~[g ∘ f]~> y -> exists{y' == y}, x ~[f ∘ g]~> y') /\
      (x ~[f ∘ g]~> y -> exists{y' == y}, x ~[g ∘ f]~> y').

  Lemma commute_sym (f g : T) :
    commute f g ->
    commute g f.
  Proof.
    unfold commute.
    intros H x y.
    destruct (H x y) as [Hxy Hyx].
    split; assumption.
  Qed.

  Lemma commute_compose (f g h : T) :
    commute f h ->
    commute g h ->
    commute (g ∘ f) h.
  Proof.
    intros Hfh Hgh a d.
    split; intros H;
      [apply mfun_assoc in H|];
      destruct H as [b [Hb [c [Hc Hd]]]].
    - (* Original: d <~[ h ∘ g ∘ f ]~ a *)
      destruct (Hgh b d) as [Hd' H_]. clear H_.
      destruct Hd' as [d' [[c' [Hbc' Hc'd']] Hdd']].
      { now exists c. }
      destruct (Hfh a c') as [Hb' H_]. clear H_.
      destruct Hb' as [c'' [Hac' Hc'c'']].
      { now exists b. }
      apply morphism_covariance with (x' := c'') in Hc'd'; [|assumption].
      destruct Hc'd' as [d'' [Hc''d'' Hd'd'']].
      exists d''.
      split.
      + sauto.
      + now rewrite Hdd', Hd'd''.
    - (* Original: d <~[ g ∘ f ∘ h ]~ a *)
      destruct (Hfh a c) as [H_ Hac']. clear H_.
      destruct Hac' as [c' [[b' [Hab' Hac']] Hcc']].
      { now exists b. }
      apply morphism_covariance with (x' := c') in Hd; [|assumption].
      destruct Hd as [d' [Hc'd' Hdd']].
      destruct (Hgh b' d') as [H_ Hb'd']. clear H_.
      destruct Hb'd' as [d'' [[c'' [Hc'' Hd'']] Hd'd'']].
      { now exists c'. }
      exists d''.
      split.
      + sauto.
      + now rewrite Hdd', Hd'd''.
  Qed.

  Program Definition id_mfun : T :=
    {| morphism := eq; |}.
  Next Obligation.
    exists x'; easy.
  Qed.

  Fixpoint compose_list (l : list T) : T :=
    match l with
    | [] => id_mfun
    | [a] => a
    | (a :: l) => compose a (compose_list l)
    end.

  Lemma compose_list_split (l1 l2 : list T) x z :
    x ~[compose_list (l1 ++ l2)]~> z ->
    exists y,
      x ~[compose_list l1]~> y /\
      y ~[compose_list l2]~> z.
  Proof.
    generalize dependent x.
    induction l1; intros x H.
    - simpl in H.
      exists x. split; easy.
    - simpl in H.
      remember (l1 ++ l2) as l.
      destruct l.
      + symmetry in Heql. destruct (app_eq_nil _ _ Heql) as [Hl1 Hl2].
        subst. exists z. firstorder.
      + destruct H as [w [Hxw Hwz]].
        rewrite Heql in *.
        destruct (IHl1 _ Hwz) as [mid [Hwmid Hmidz]].
        exists mid. split.
        2:{ assumption. }
        destruct l1.
        * simpl in *. subst. assumption.
        * simpl. exists w; firstorder.
  Qed.

  Lemma compose_list_app (l1 l2 : list T) x y z :
    x ~[compose_list l1]~> y ->
    y ~[compose_list l2]~> z ->
    x ~[compose_list (l1 ++ l2)]~> z.
  Proof.
    generalize dependent x. generalize dependent y.
    induction l1; intros x y Hl1 Hl2.
    - simpl in *. subst. assumption.
    - destruct l1.
      + simpl in Hl1.
        destruct l2 as [|g l2].
        * simpl in *. now subst.
        * exists x.
          rewrite app_nil_l.
          firstorder.
      + destruct Hl1 as [w [Hyw Hwx]].
        specialize (IHl1 x w Hwx Hl2).
        exists w. firstorder.
  Qed.

  Lemma comm_permutation (l l' : list T) x y :
    RestrictedPermutation commute l l' ->
    x ~[compose_list l]~> y ->
    exists{y' == y}, x ~[compose_list l']~> y'.
  Proof.
    intros Hperm. generalize dependent x. generalize dependent y.
    induction Hperm as [| f l1 l2 | |]; intros y x.
    { simpl. exists y. subst. split; reflexivity. }
    { intros Hfl1.
      replace (f :: l1) with ([f] ++ l1) in Hfl1 by reflexivity.
      apply compose_list_split in Hfl1. destruct Hfl1 as [w [Hxw Hwy]].
      specialize (IHHperm y w Hwy). destruct IHHperm as [z [Hwz Hz]].
      exists z. split.
      - replace (f :: l2) with ([f] ++ l2) by reflexivity.
        eapply compose_list_app; now eauto.
      - assumption.
    }
    { replace (a :: b :: l) with ([a; b] ++ l) by reflexivity.
      replace (b :: a :: l) with ([b; a] ++ l) by reflexivity.
      intros Hxy.
      apply compose_list_split in Hxy. destruct Hxy as [w [Hxw Hwy]].
      destruct (H x w) as [Hcomm _].
      destruct Hcomm as [v [Hxv Hv]].
      - inversion Hxw. firstorder.
      - morph_shift (compose_list l) v.
        exists y'.
        split.
        + eapply compose_list_app; eauto.
        + assumption.
    }
    { intros Hl.
      eapply IHHperm1 in Hl. destruct Hl as [y1 [Hxy1 Hyy1]].
      eapply IHHperm2 in Hxy1. destruct Hxy1 as [y2 [Hy2 Hy1y2]].
      exists y2. split.
      - assumption.
      - rewrite Hyy1, Hy1y2. reflexivity.
    }
  Qed.
End props.

Fact eq_setoid_commutative {A} (a b : @MFun A A (eq_setoid A) (eq_setoid A)) :
  eq_commute a b <-> commute a b.
Proof.
  split; unfold commute, eq_commute.
  - sauto.
  - intros H x z. specialize (H x z).
    sauto.
Qed.

(** ** Product of multfunctions *)
Section mfun_prod.
  Context {A B C D : Type} `{setoidA : Setoid A} `{setoidB : Setoid B} `{setoidC : Setoid C} `{setoidD : Setoid D}.

  Program Definition mfun_prod (f : @MFun A B setoidA setoidB) (g : @MFun C D setoidC setoidD) :
    @MFun (A * C) (B * D) (pair_setoid A C) (pair_setoid B D) :=
    {| morphism x y :=
        let (x_l, x_r) := x in
        let (y_l, y_r) := y in
        morphism f x_l y_l /\ morphism g x_r y_r;
    |}.
  Next Obligation.
    morph_shift f a.
    morph_shift g c.
    exists (b', d'). sauto.
  Qed.
End mfun_prod.

(** ** Sum of multfunctions *)
Section mfun_sum.
  Context {A A' B : Type} `{setoidA : Setoid A} `{setoidA' : Setoid A'} `{setoidB : Setoid B}.

  Program Definition mfun_sum_l (f : @MFun A A' setoidA setoidA') :
    @MFun (A * B) (A' * B) (pair_setoid A B) (pair_setoid A' B) :=
    {| morphism x y :=
        let (x_l, x_r) := x in
        let (y_l, y_r) := y in
        morphism f x_l y_l /\ x_r = y_r
    |}.
  Next Obligation.
    morph_shift f a0.
    exists (a', b0).
    sauto.
  Qed.

  Program Definition mfun_sum_r (f : @MFun A A' setoidA setoidA') :
    @MFun (B * A) (B * A') (pair_setoid B A) (pair_setoid B A') :=
    {| morphism x y :=
        let (x_l, x_r) := x in
        let (y_l, y_r) := y in
        x_l = y_l /\ morphism f x_r y_r
    |}.
  Next Obligation.
    morph_shift f a0.
    exists (b0, a').
    sauto.
  Qed.
End mfun_sum.

(** ** Lifting constant to [MFun] *)

Section const.
  Context {T : Type}.

  Program Definition mfun_const (a : T) : MFun True T :=
    {|
      morphism _ ret := ret = a;
    |}.
  Next Obligation.
    now exists a.
  Qed.
End const.

(** ** Lifting pure function to [MFun] *)
Section pure.
  Context {Dom Cod : Type}
    `{setoidDom : Setoid Dom}
    `{setoidCod : Setoid Cod}
    (f : Dom -> Cod)
    (f_covariance : forall a a',
        a == a' ->
        f a == f a').

  Program Definition pure : MFun Dom Cod :=
    {|
      morphism a b := f a = b;
    |}.
  Next Obligation.
    exists (f x').
    split.
    - reflexivity.
    - now apply f_covariance.
  Qed.
End pure.

Lemma pure_commutativity {T} `{setoidT : Setoid T}
  (f g : T -> T)
  f_covariance g_covariance
  (H : forall x, f (g x) == g (f x)) :
  commute (pure f f_covariance) (pure g g_covariance).
Proof.
  unfold pure, commute.
  intros x z.
  split; intros Hxz;
    destruct Hxz as [y [Hy Hz]];
    simpl in *;
    subst.
  - exists (f (g x)). split.
    + now exists (g x).
    + symmetry. apply H.
  - exists (g (f x)). split.
    + now exists (f x).
    + apply H.
Qed.

(** ** Multi-valued function with return value

 [MFunRet] is a helper that defines a multi-valued function that
 returns a value of type [Ret] while updating [State].

 It is equivalent to pure function of type [State -> Ret * State].
*)
Section MFunRet.
  Context (Ret State : Type) `{HRet : Setoid Ret} `{HState : Setoid State}.

  Definition MFunRet := @MFun State (Ret * State)
                          HState (@pair_setoid _ _ HRet HState).

  Inductive MFunRet_drop (f : MFunRet) : State -> State -> Prop :=
  | MFunRet_drop_ : forall s s' ret,
      s ~[f]~> (ret, s') ->
      MFunRet_drop f s s'.

  Program Definition MFunRet_drop_ret (f : MFunRet) : @MFun State State HState HState :=
    {| morphism := MFunRet_drop f |}.
  Next Obligation.
    inversion_clear H0.
    apply morphism_covariance with (x' := x') in H1; [|assumption].
    destruct H1 as [[ret' y'] [Hy' Hyy']].
    destruct Hyy'.
    exists y'. sauto.
  Qed.
End MFunRet.

Definition MFunRet_commute {State Ret1 Ret2}
  `{Hss : Setoid State}
  `{Hsr1 : Setoid Ret1}
  `{Hsr2 : Setoid Ret2}
  (f : MFunRet Ret1 State)
  (g : MFunRet Ret2 State) :=
  commute (MFunRet_drop_ret _ _ f) (MFunRet_drop_ret _ _ g).

Section lift_mfun_option.
  Context {A B C : Type} (f : MFun A (option B)) (g : B -> C).

  Inductive LiftMFunOption : A -> option C -> Prop :=
  | LiftMFunOption_None : forall a,
      a ~[f]~> None ->
      LiftMFunOption a None
  | LiftMFunOption_Some : forall a b,
      a ~[f]~> Some b ->
      LiftMFunOption a (Some (g b)).

  Program Definition mfun_option_lift_pure : MFun A (option C) :=
    {| morphism := LiftMFunOption |}.
  Next Obligation.
    destruct y as [c|].
    - inversion_clear H0.
      unfold exists_equiv.
      exists (Some (g b)); sauto.
    - inversion_clear H0.
      exists None. sauto.
  Qed.
End lift_mfun_option.
