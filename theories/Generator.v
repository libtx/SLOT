(* SLOT, a formally verified model-checker
   Copyright (C) 2019-2021, 2023  k32

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, version 3 of the License.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

(** * Ensembles that can be deconstructed one element at a time
 *)

From Coq Require Import
     List
     Lia.

Import ListNotations.

From SLOT Require Import
     Foundations
     Commutativity
     Properties
     Tactics.

From Hammer Require Import
     Tactics.

Class Generator TE g :=
  { gen_step : g -> option (g * TE) -> Prop
  }.

Open Scope slot_scope.

Notation "A '~~>' B & C" := (gen_step A (Some (B, C))) (at level 20) : slot_scope.

Notation "A '~~>x'" := (gen_step A None) (at level 20) : slot_scope.

Section GenEnsemble.
  (** Generator as an ensemble *)
  Context {TE G : Type} `{Generator TE G}.

  Inductive GenEnsemble (g : G) : @TraceEnsemble TE :=
  | gen_ens_nil :
      g ~~>x ->
      GenEnsemble g []
  | gen_ens_cons : forall g' te t,
      g ~~> g' & te ->
      GenEnsemble g' t ->
      GenEnsemble g (te :: t).
End GenEnsemble.

Section gen_commutativity.
  Context {TE} Gen `{Generator (ProcessEvent TE) Gen}.

  Definition different_processes {Evt} (te1 te2 : ProcessEvent Evt) :=
    match te1, te2 with
      pid1 @ _, pid2 @ _ => pid1 <> pid2
    end.

  Definition generator_events_commute :=
    forall g g' g'' te1 te2,
      different_processes te1 te2 ->
      g ~~> g' & te1 ->
      g' ~~> g'' & te2 ->
      exists g_,
        g ~~> g_ & te2 /\ g_ ~~> g'' & te1.
End gen_commutativity.

Section list_defn.
  Context (A : Type).

  Let G := list A.

  Inductive ListGenStep : G -> option (G * A) -> Prop :=
  | lgen_nil :
      ListGenStep [] None
  | lgen_cons : forall te t,
      ListGenStep (te :: t) (Some (t, te)).

  Global Instance listGenerator : Generator A G :=
    { gen_step := ListGenStep }.

  Lemma list_gen_correct : forall l l',
      GenEnsemble l l' ->
      l = l'.
  Proof.
    intros.
    induction H.
    - now inversion H.
    - subst. now inversion_clear H.
  Qed.
End list_defn.

Section process.
  Section defn.
    Context {Request : Type} {Reply : Request -> Type}.

    Let TE := IOp Request Reply.
    Let t := @Program Request Reply.

    Definition ThreadGenStep (gen : t) (next : option (t * TE)) : Prop :=
      match gen with
      | p_dead =>
          next = None
      | p_cont req cont =>
          exists (ret : Reply req),
          next = Some (cont ret, ret <~ req)
      end.

    Global Instance processGen : Generator TE t :=
    { gen_step := ThreadGenStep }.
  End defn.

  Section tests.
    Let Req := bool.
    Let Rep req :=
      match req with
      | true => nat
      | false => bool
      end.

    Let my_prog : @Program Req Rep :=
      do x <- true;
      match x with
      | 0 =>
        done false
      | _ =>
        done true
      end.

    Goal forall t,
        GenEnsemble my_prog t ->
        exists x y z,
          t = [0 <~ true; x <~ false] \/
          t = [S y <~ true; z <~ true].
    Proof.
      intros. subst my_prog. simpl.
      sauto.
    Qed.
  End tests.
End process.

Section singleton_process.
  Context {Gen State Event} `{StateSpace State (ProcessEvent Event)} `{Generator Event Gen}.

  Record SingletonProcess :=
    singleton_process { _ : Gen }.

  Inductive SingletonStep : SingletonProcess -> option (SingletonProcess * (ProcessEvent Event)) -> Prop :=
  | wrs_nil : forall g,
      g ~~>x ->
      SingletonStep (singleton_process g) None
  | wrp_cons : forall g g' evt,
      g ~~> g' & evt ->
      SingletonStep (singleton_process g) (Some (singleton_process g', 0 @ evt)).

  Global Instance singletonGen : Generator (ProcessEvent Event) SingletonProcess :=
    { gen_step := SingletonStep }.

  Lemma singleton_gen_comm :
    generator_events_commute SingletonProcess.
  Proof.
    intros g g' g'' te1 te2 Hpids Hg Hg'.
    exfalso.
    inversion Hg; inversion Hg'; subst.
    sauto.
  Qed.
End singleton_process.

#[export] Hint Resolve singleton_gen_comm : slot.

Section parallel_defn.
  Context {TE G__l G__r : Type} `{Generator TE G__l} `{Generator (ProcessEvent TE) G__r}.

  Record Parallel :=
    parallel
      { gp_l : G__l;
        gp_r : G__r
      }.

  Inductive ParallelStep : Parallel -> option (Parallel * (ProcessEvent TE)) -> Prop :=
  | g_left : forall te g__l g__l' g__r,
      g__l ~~> g__l' & te ->
      ParallelStep (parallel g__l g__r) (Some (parallel g__l' g__r, 0 @ te))
  | g_right : forall te pid g__l g__r g__r',
      g__r ~~> g__r' & (pid @ te) ->
      ParallelStep (parallel g__l g__r) (Some (parallel g__l g__r', S pid @ te))
  | g_nil : forall g__l g__r,
      g__l ~~>x ->
      g__r ~~>x ->
      ParallelStep (parallel g__l g__r) None.

  Global Instance genPairGen : Generator (ProcessEvent TE) Parallel :=
    { gen_step := ParallelStep }.
End parallel_defn.

Infix "<||>" := parallel (right associativity, at level 101) : slot_scope.
Notation "[| x |]" := (singleton_process x) : slot_scope.
Notation "[| x ; .. ; y ; z |]" := (parallel x (.. (parallel y (singleton_process z)) ..)) : slot_scope.

Section parallel_tests.
  (* Check that all interleavings created by the ensemble are valid: *)
  Goal forall t,
      GenEnsemble [| [1; 2]; [3] |] t ->
      t = [0 @ 1; 0 @ 2; 1 @ 3] \/
      t = [0 @ 1; 1 @ 3; 0 @ 2] \/
      t = [1 @ 3; 0 @ 1; 0 @ 2].
  Proof.
    intros. sauto.
  Qed.

  (* Check that it creates every interleaving: *)
  Goal GenEnsemble [| [1; 2]; [3] |] [0 @ 1; 0 @ 2; 1 @ 3].
  Proof.
    constructor 2 with (g' := [| [2]; [3] |]).
    - sauto.
    - constructor 2 with (g' := [| []; [3] |]); sauto.
  Qed.

  Goal GenEnsemble [| [1; 2]; [3] |] [0 @ 1; 1 @ 3; 0 @ 2].
  Proof.
    constructor 2 with (g' := [| [2]; [3] |]).
    - sauto.
    - constructor 2 with (g' := [| [2] ; [] |] ); sauto.
  Qed.

  Goal GenEnsemble [| [1; 2] ; [3] |] [1 @ 3; 0 @ 1; 0 @ 2].
  Proof.
    constructor 2 with (g' := [| [1; 2] ; [] |]).
    - sauto.
    - constructor 2 with (g' := [| [2] ; [] |]); sauto.
  Qed.

  Goal forall t,
      GenEnsemble [| [3] ; [1; 2] |] t ->
      t = [1 @ 1; 1 @ 2; 0 @ 3] \/
      t = [1 @ 1; 0 @ 3; 1 @ 2] \/
      t = [0 @ 3; 1 @ 1; 1 @ 2].
  Proof.
    intros. sauto.
  Qed.

  (* Test interleavings of larger system *)
  Goal forall t,
      GenEnsemble [| [1; 2]; [3; 4] |] t ->
      t = [0 @ 1; 0 @ 2; 1 @ 3; 1 @ 4] \/
      t = [0 @ 1; 1 @ 3; 0 @ 2; 1 @ 4] \/
      t = [0 @ 1; 1 @ 3; 1 @ 4; 0 @ 2] \/

      t = [1 @ 3; 0 @ 1; 0 @ 2; 1 @ 4] \/
      t = [1 @ 3; 0 @ 1; 1 @ 4; 0 @ 2] \/
      t = [1 @ 3; 1 @ 4; 0 @ 1; 0 @ 2].
  Proof.
    intros. sauto.
  Qed.

  (* Test interleavings of a system with 3 processes *)
  Goal forall t,
      GenEnsemble [| [0]; [1]; [2] |] t ->
      t = [0 @ 0; 1 @ 1; 2 @ 2] \/
      t = [0 @ 0; 2 @ 2; 1 @ 1] \/

      t = [1 @ 1; 0 @ 0; 2 @ 2] \/
      t = [1 @ 1; 2 @ 2; 0 @ 0] \/

      t = [2 @ 2; 1 @ 1; 0 @ 0] \/
      t = [2 @ 2; 0 @ 0; 1 @ 1].
  Proof.
    intros. sauto.
  Qed.
End parallel_tests.

From SLOT Require Import
     Properties.

From Coq Require Import
     Classical_Prop.

Section optimize.
  Context {Gen State Event : Type}.
  Let TE := (ProcessEvent Event).
  Context `{Hssp : StateSpace State TE} `{Hgen : Generator TE Gen}.

  Definition can_follow (te1 te2 : TE) : Prop :=
    let (pid1, _) := te1 in
    let (pid2, _) := te2 in
    pid1 <= pid2 \/ not (events_commute te1 te2).

  Inductive GenEnsembleOpt (g : Gen) : @TraceEnsemble TE :=
  | og_ens_nil :
      g  ~~>x ->
      GenEnsembleOpt g []
  | og_ens_first : forall g' te,
      g  ~~> g' & te ->
      g' ~~>x ->
      GenEnsembleOpt g [te]
  | og_ens_cons : forall g' te te' t,
      g ~~> g' & te ->
      can_follow te te' ->
      GenEnsembleOpt g' (te' :: t) ->
      GenEnsembleOpt g (te :: te' :: t).

  Fixpoint gen_ens_opt_add g g' te te' t (Hte : g ~~> g' & te)
           (Ht : GenEnsembleOpt g' (te' :: t))
           (HG : generator_events_commute Gen)
           (Hfoll : ~ can_follow te te') {struct Ht} :
    exists t' : list TE, GenEnsembleOpt g (te' :: t') /\ Permutation events_commute (te :: te' :: t) (te' :: t').
  Proof with auto with slot.
    destruct te as [pid evt]. destruct te' as [pid' evt'].
    firstorder. apply NNPP in H0. rename H0 into Hcomm.
    assert (Hpids : pid <> pid') by lia.
    inversion Ht; subst; clear Ht.
    - exists [pid @ evt]. split.
      + specialize (HG g g' g'0 (pid @ evt) (pid' @ evt') Hpids).
        destruct HG as [g_ [Hg_ Hg_']]...
        constructor 3 with g_...
        * left. lia.
        * constructor 2 with g'0...
      + constructor 3...
    - specialize (HG g g' g'0 (pid @ evt) (pid' @ evt') Hpids) as Hgen_comm.
      destruct Hgen_comm as [g_ [Hg_ Hg_']]...
      destruct (classic (can_follow (pid @ evt) te')) as [Hfoll' | Hfoll'].
      + exists (pid @ evt :: te' :: t0). split.
        * constructor 3 with g_...
          -- left. lia.
          -- constructor 3 with g'0...
        * constructor 3...
      + specialize (gen_ens_opt_add g_ g'0 (pid @ evt) te' t0) as IH. clear gen_ens_opt_add.
        destruct IH as [t' [Ht' Hperm']]...
        exists (te' :: t'). split.
        * constructor 3 with g_...
        * sauto.
  Qed.

  Fixpoint gen_ens_opt (g : Gen) (t : list TE) (Ht : GenEnsemble g t)
           (HG : generator_events_commute Gen)
           {struct Ht} :
    exists t' : list TE, GenEnsembleOpt g t' /\ Permutation events_commute t t'.
  Proof with auto with slot.
    destruct Ht as [Hnil | g' te t Hte Ht].
    - exists []. split; now constructor.
    - apply gen_ens_opt in Ht. destruct Ht as [t' [Ht' Hperm]]; clear gen_ens_opt.
      destruct t' as [ | te' t'].
      + exists [te].
        apply perm_empty in Hperm; subst.
        split.
        * inversion Ht'. constructor 2 with g'...
        * repeat constructor.
      + destruct (classic (can_follow te te')).
        * exists (te :: te' :: t'). split.
          -- constructor 3 with g'...
          -- now constructor.
        * eapply gen_ens_opt_add in Ht'; eauto.
          destruct Ht' as [t'' [Ht'' Hperm'']].
          exists (te' :: t''). split.
          -- assumption.
          -- apply perm_trans with (te :: te' :: t')...
      + assumption.
  Qed.

  Theorem optimize_gen_p g
    (HG : generator_events_commute Gen) :
    sufficient_replacement_p (GenEnsemble g) (GenEnsembleOpt g).
  Proof.
    intros t Ht.
    now apply gen_ens_opt.
  Qed.

  Theorem optimize_gen (g : Gen) P Q (HG : generator_events_commute Gen) :
    -{{ P }} GenEnsembleOpt g {{ Q }} ->
    -{{ P }} GenEnsemble g {{ Q }}.
  Proof.
    now apply ht_sufficient_replacement, comm_perm_sufficient_replacement, optimize_gen_p.
  Qed.
End optimize.

Section parallel_gen_comm.
  Context {State Event} `{StateSpace State (ProcessEvent Event)} {G1 G2}
          `{Generator Event G1}
          `{Generator (ProcessEvent Event) G2}.

  Lemma parallel_gen_comm :
    generator_events_commute G2 ->
    generator_events_commute (@Parallel G1 G2).
  Proof.
    intros HG2 g g' g'' te1 te2 Hpids Hg Hg'.
    destruct te1 as [pid1 evt1]. set (te1 := pid1 @ evt1).
    destruct te2 as [pid2 evt2]. set (te2 := pid2 @ evt2).
    simpl in Hpids.
    inversion Hg; inversion Hg'; subst.
    - exfalso. lia.
    - sauto.
    - sauto.
    - assert (Hpids' : different_processes (pid @ evt1) (pid0 @ evt2)).
      { simpl. lia. }
      inversion H8; subst.
      specialize (HG2 g__r g__r' g__r'0).
      specialize (HG2 (pid @ evt1) (pid0 @ evt2) Hpids').
      specialize (HG2 H4 H9).
      sauto.
  Qed.

  Theorem parallel_processes_ht :
    forall (P Q : State -> Prop) (g1 : G1) (g2 : G2),
      generator_events_commute G2 ->
      -{{ P }} GenEnsembleOpt (g1 <||> g2) {{ Q }} ->
      -{{ P }} GenEnsemble (g1 <||> g2) {{ Q }}.
  Proof.
    intros *. intros HG2 Hht.
    apply parallel_gen_comm in HG2.
    specialize (optimize_gen (g1 <||> g2) P Q HG2 Hht) as Hopt.
    assumption.
  Qed.
End parallel_gen_comm.

#[export] Hint Unfold can_follow : slot.
#[export] Hint Resolve singleton_gen_comm : slot.
#[export] Hint Resolve parallel_gen_comm : slot.
