(** * Token Machine

 Token machine class describes a class of nondeterministic state
 automata, where type [Event] enumerates all state transitions.
 Each value of [Event] is mapped to [MFun state state].
 *)
From Stdlib Require Import
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
  Setoids
  RestrictedPermutation
  Multifunction.

Import ListNotations.

(** ** Canonical order of events

 A binary relation to compare events less or equal.
 *)
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

  Lemma event_commute_sym (a b : Event) :
    event_commute a b ->
    event_commute b a.
  Proof.
    intros H.
    unfold event_commute in *.
    now apply commute_sym.
  Qed.

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

  Lemma canon_trace_add x y y' z f t (Hf : x ~[tm_state_trans f]~> y)
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
         the [f ∘ g] path: *)
      assert (exists{v' == v}, x ~[tm_state_trans f ∘ tm_state_trans g]~> v') as Hv'. {
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
