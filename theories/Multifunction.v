From Coq Require Import
  Program
  Decidable
  List
  Ensembles
  Relation_Definitions
  RelationClasses
  SetoidClass
  SetoidDec
  Classes.Morphisms.

From Hammer Require Import
  Tactics.

From SLOT Require Import
  RestrictedPermutation.

Import ListNotations.

Section exists_equiv.
  Context {S : Type} `{Setoid S}.

  Definition exists_equiv (prop : S -> Prop) (s : S) : Prop :=
    exists (s' : S), prop s' /\ s == s'.
End exists_equiv.

Notation "'exists{' A == B } , C" :=
  (exists_equiv (fun A => C) B)
  (at level 300, A name, B name, C at level 300, right associativity) : type_scope.

Hint Unfold exists_equiv : slot.

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

Global Arguments morphism {_ _ _ _}.
Global Arguments morphism_covariance {_ _ _ _}.

Declare Scope slot_scope.
Open Scope slot_scope.

Notation "A '~[' B ']~>' C" := (morphism B A C) (at level 20) : slot_scope.

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

Infix "∘" := compose : slot_scope.

Section props.
  Context {A : Type} `{Hsetoid : Setoid A}.
  Let T := @MFun A A Hsetoid Hsetoid.

  (* Strong definition of commutativity based on equality *)
  Definition eq_commute (f g : T) :=
    forall (x y : A), x ~[f ∘ g]~> y <-> x ~[g ∘ f]~> y.

  (* Relaxed version of the above based on equivalence *)
  Definition commute (f g : T) :=
    forall x y,
      (x ~[f ∘ g]~> y -> exists{y' == y}, x ~[g ∘ f]~> y') /\
      (x ~[g ∘ f]~> y -> exists{y' == y}, x ~[f ∘ g]~> y').

  Program Definition id_mfun : T :=
    {| morphism := eq; |}.
  Next Obligation.
    exists x'; easy.
  Qed.

  Fixpoint compose_list (l : list T) : T :=
    match l with
    | [] => id_mfun
    | [a] => a
    | (a :: l) => a ∘ compose_list l
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

Section mfun_prod.
  Context {A B C D : Type} `{setoidA : Setoid A} `{setoidB : Setoid B} `{setoidC : Setoid C} `{setoidD : Setoid D}.

  Program Definition mfun_prod (f : @MFun A B setoidA setoidB) (g : @MFun C D setoidC setoidD) :
    @MFun (A * C) (B * D) (setoidPair A C) (setoidPair B D) :=
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

Section mfun_sum.
  Context {A A' B : Type} `{setoidA : Setoid A} `{setoidA' : Setoid A'} `{setoidB : Setoid B}.

  Program Definition mfun_sum_l (f : @MFun A A' setoidA setoidA') :
    @MFun (A * B) (A' * B) (setoidPair A B) (setoidPair A' B) :=
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
    @MFun (B * A) (B * A') (setoidPair B A) (setoidPair B A') :=
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

Section canonical_order.
  Context {A : Type}.

  Class CanonicalOrder (canon_rel : relation A) := {
      canon_rel_dec a b : decidable (canon_rel a b);

      canon_rel_total a b : canon_rel a b \/ canon_rel b a;
    }.
End canonical_order.

Section token_machine.
  Context {State : Type}.

  Class TokenMachine {Event : Type} :=
    {
      tm_setoid :: Setoid State;
      tm_canon_rel : relation Event;
      tm_canon_order :: CanonicalOrder tm_canon_rel;
      tm_state_trans : Event -> @MFun State State tm_setoid tm_setoid;
    }.
End token_machine.

Section token_trace_ensemble.
  Context `{Hts : TokenMachine}.

  Definition Trace := list Event.

  Definition TraceEnsemble := Ensemble Trace.

  Definition event_commute (a b : Event) := commute (tm_state_trans a) (tm_state_trans b).

  Definition sufficient_replacement_p (e e' : TraceEnsemble) :=
    forall t, e t ->
         exists t', e' t' /\ RestrictedPermutation event_commute t t'.

  Lemma sufficient_replacement_p_trans : Transitive sufficient_replacement_p.
  Proof.
    unfold Transitive,sufficient_replacement_p.
    intros x y z Hxy Hyz t Ht_in_x.
    destruct (Hxy t Ht_in_x) as [t' [Ht'_in_y Htt']].
    destruct (Hyz t' Ht'_in_y) as [t'' [Ht''_in_z Ht't'']].
    exists t''. split.
    - assumption.
    - now constructor 4 with (l' := t').
  Qed.
End token_trace_ensemble.

Section canonical_trace.
  Context `{Hts: TokenMachine}.

  Context (commut_dec : forall f g, decidable (event_commute f g)).

  Definition can_follow (a b : Event) :=
    event_commute a b -> tm_canon_rel a b.

  Lemma can_follow_dec a b : decidable (can_follow a b).
  Proof.
    unfold can_follow.
    specialize (commut_dec a b) as Hdcomm.
    apply dec_imp.
    - assumption.
    - apply canon_rel_dec.
  Qed.

  Definition can_follow_hd (token : Event) (trace : Trace) : Prop :=
    match trace with
    | [] => True
    | head :: _ =>
        can_follow token head
    end.

  Lemma can_follow_hd_dec a t : decidable (can_follow_hd a t).
  Proof.
    destruct t.
    - simpl. apply dec_True.
    - simpl. apply can_follow_dec.
  Qed.

  Inductive CanonicalTrace : Trace -> relation State :=
  | canontr_nil : forall s,
      CanonicalTrace [] s s
  | canontr_cons : forall s s' s'' token trace,
      s ~[tm_state_trans token]~> s' ->
      can_follow_hd token trace ->
      CanonicalTrace trace s' s'' ->
      CanonicalTrace (token :: trace) s s''.

  Program Definition mfunCanonTrace t := {| morphism := CanonicalTrace t |}.
  Next Obligation.
    generalize dependent x'.
    induction H0 as [|x y z f t Hfxy Hfollow Ht IH].
    - sauto.
    - intros a2 Hx.
      morph_shift (tm_state_trans f) a2.
      destruct (IH y' Hequiv_y_y') as [z' [Hy'z' Hzz']].
      exists z'. split.
      + constructor 2 with (s' := y'); sauto.
      + assumption.
  Qed.

  Lemma can_follow_hd_eq {te t1 t2} (Hfoll : can_follow_hd te t1) (Hhd : hd_error t1 = hd_error t2) :
    can_follow_hd te t2.
  Proof.
    intros.
    unfold can_follow_hd in *.
    destruct t1, t2; try reflexivity.
    - exfalso. inversion Hhd.
    - simpl in Hhd. injection Hhd as H. now subst.
  Qed.

  Lemma  canon_trace_add x y y' z f t (Hf : x ~[tm_state_trans f]~> y)
                         (Hy' : y == y')
                         (Ht : CanonicalTrace t y' z)
                         (Hfoll : ~can_follow_hd f t) :
    exists t', exists{z' == z},
      CanonicalTrace t' x z' /\
      RestrictedPermutation event_commute (f :: t) t' /\
        (hd_error t = hd_error t').
  Proof.
    generalize dependent x. generalize dependent y.
    induction Ht as [|y' v z g t' Hy'v Hfoll' Ht'].
    - exfalso.
      unfold not, can_follow_hd in Hfoll.
      contradiction.
    - intros y Hyy' x Hxy. simpl in Hfoll.
      assert (Hfg_canon : tm_canon_rel g f). {
        assert (Hcanon_total : tm_canon_rel f g \/ tm_canon_rel g f) by
          apply canon_rel_total.
        firstorder.
      }
      assert (Hfg_comm : event_commute f g). {
        unfold can_follow_hd, can_follow in Hfoll.
        destruct (commut_dec f g).
        - assumption.
        - firstorder.
      }
      (* Use commutativity to derive an intermediate state on
         the [g ∘ f] path: *)
      assert (exists{v' == v}, x ~[tm_state_trans g ∘ tm_state_trans f]~> v') as Hv'. {
        morph_shift (tm_state_trans g) y.
        destruct (Hfg_comm x v') as [Hcomm _].
        destruct Hcomm as [w Hw].
        { exists y. firstorder. }
        exists w. split.
        - firstorder.
        - destruct Hw as [_ H1]. now rewrite Hequiv_v_v', H1.
      }
      destruct Hv' as [v' [Hxv' Hvv']].
      specialize (morphism_covariance (mfunCanonTrace t') v v' z Hvv' Ht') as Hw'.
      destruct Hw' as [w' [Hw' Hww']].
      (* Case analysis: can we add attach [g] to [t']? *)
      destruct (can_follow_hd_dec f t').
      { (* Yes, we can. Proof by construction: *)
        exists (g :: f :: t'). clear IHHt'.
        destruct Hxv' as [u [Hg' Hf']].
        exists w'. repeat split.
        - constructor 2 with (s' := u).
          + assumption.
          + simpl. now unfold can_follow.
          + constructor 2 with (s' := v'); assumption.
        - now constructor.
        - assumption.
      }
      { (* No, we cannot. Proof by induction: *)
        destruct Hxv' as [u' [Hxu' Hv'u']].
        symmetry in Hvv'.
        specialize (IHHt' H v' Hvv' u' Hv'u').
        destruct IHHt' as [t'' [z' Ht'']].
        destruct Ht'' as [[Ht'' [Hpermt'' Hhd]] Hzz'].
        exists (g :: t''). exists z'. repeat split.
        - (* Prove that [g :: t''] is a canonical trace from [x] to
          [z'] *)
          constructor 2 with (s' := u'); auto.
          eapply can_follow_hd_eq; eauto.
        - (* Prove that it's possible to go from [f :: g :: t'] to
          [g :: t''] by swapping commiting events: *)
          assert (RestrictedPermutation event_commute (g :: f :: t') (g :: t'')) by
            now constructor 2.
          assert (RestrictedPermutation event_commute (f :: g :: t') (g :: f :: t')) by
            now constructor 3.
          econstructor 4; eauto.
        - assumption.
      }
  Qed.

  Theorem canonicalize_trace x z :
    sufficient_replacement_p
      (fun t => x ~[compose_list (map tm_state_trans t)]~> z)
      (fun t => exists{z' == z}, CanonicalTrace t x z').
  Proof.
    intros t Ht. generalize dependent z. generalize dependent x.
    induction t as [|f t].
    { intros. simpl in Ht. subst.
      exists []. split.
      - exists z. sauto.
      - constructor.
    }
    { intros x y Hxy.
      destruct t as [|g t].
      - simpl in Hxy. exists [f]. split.
        + exists y. split.
          * constructor 2 with (s' := y); [easy | easy | now constructor].
          * reflexivity.
        + repeat constructor.
      - destruct Hxy as [w [Hxw Hwy]].
        eapply IHt in Hwy.
        destruct Hwy as [t' [[y' [Hcanont' Hyy']] Hpermt']].
        destruct (can_follow_hd_dec f t').
        + exists (f :: t'). split.
          * exists y'. split.
            -- constructor 2 with (s' := w); assumption.
            -- assumption.
          * now constructor.
        + clear IHt.
          eapply canon_trace_add in Hcanont'; eauto.
          destruct Hcanont' as [t'' [y'' [Ht'' Hy'']]].
          destruct Ht'' as [Ht'' [Hperm Hhd]].
          exists t''. split.
          * exists y''. split.
            -- assumption.
            -- rewrite Hyy', Hy''. reflexivity.
          * assert (RestrictedPermutation event_commute (f :: g :: t) (f :: t')) by
              now constructor 2.
            econstructor 4; eauto.
          * reflexivity.
    }
  Qed.
End canonical_trace.

Section TransitionSystem.
  Context {State : Type}.

  Definition ts_ret (Event : Type) := option (Event * State).

  Definition ts_ret_setoid (Event : Type) (Hss : Setoid State) :=
    let sp := @setoidPair Event State (eq_setoid _) Hss in
    @setoid_option (Event * State) sp.

  Class TransitionSystem {Event : Type} :=
    {
      ts_setoid :: Setoid State;
      ts_canon_rel : relation Event;
      ts_canon_order :: CanonicalOrder ts_canon_rel;
      ts_state_trans :: @MFun State (ts_ret Event) ts_setoid (ts_ret_setoid Event ts_setoid);
    }.

  Program Definition tsg_mfun `{TransitionSystem} (e : Event) : MFun State State :=
    {| morphism s s' :=
        s ~[ts_state_trans]~> Some (e, s');
    |}.
  Solve All Obligations with sauto.

  Global Instance tsTokenSystem `{TransitionSystem} : @TokenMachine State Event :=
    { tm_setoid := ts_setoid;
      tm_canon_rel := ts_canon_rel;
      tm_canon_order := ts_canon_order;
      tm_state_trans := tsg_mfun;
    }.
End TransitionSystem.

Section TSProps.
  Context `{HTS : TransitionSystem}
           (Hcanon_dec : forall f g : Event, decidable (event_commute f g)).

  (* TODO: this is an mfun *)
  Inductive TSMFunGen : State -> list Event -> State -> Prop :=
  | ts_nil : forall s,
      s ~[ts_state_trans]~> None ->
      TSMFunGen s [] s
  | ts_cont : forall s s' s'' t event,
      TSMFunGen s' t s'' ->
      s ~[ts_state_trans]~> Some (event, s') ->
      TSMFunGen s (event :: t) s''.

  Lemma transition_system_as_token_machine_trace (s s' : State) (t : list Event) :
    TSMFunGen s t s' ->
      s ~[compose_list (map tm_state_trans t)]~> s'.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - destruct t; simpl in *.
      + inversion H. now subst.
      + exists s'. now split.
  Qed.

  Inductive CanonicalTSMFunGen : State -> list Event -> State -> Prop :=
  | cts_nil : forall s,
      s ~[ts_state_trans]~> None ->
      CanonicalTSMFunGen s [] s
  | cts_cons : forall s s' s'' event trace,
      s ~[ts_state_trans]~> Some (event, s') ->
      can_follow_hd event trace ->
      CanonicalTSMFunGen s' trace s'' ->
      CanonicalTSMFunGen s (event :: trace) s''.

  Theorem canonicalize_transition_system : forall s s' t,
      TSMFunGen s t s' ->
      exists t', exists{s'' == s'},
        CanonicalTSMFunGen s t' s''.
  Proof.
    intros.
    specialize (transition_system_as_token_machine_trace s s' t H) as Hss'.
    specialize (canonicalize_trace Hcanon_dec s s' t) as Hcan.
    simpl in Hcan. apply Hcan in Hss'. clear Hcan.
    destruct Hss' as [t' Ht'].
    exists t'.
    destruct Ht' as [[s'' [Hss'' Heq]] Ht'].
    exists s''.
    split; [|assumption].
    generalize dependent t.
    induction Hss''.
    - constructor.
      apply perm_empty in Ht'.
      inversion H; subst; sauto.
    - specialize (IHHss'' Heq).
      intros.




End TSProps.
