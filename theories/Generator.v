(* SLOT, a formally verified model-checker
   Copyright (C) 2019-2021  k32

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
     List.

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

Module Empty.
  Section defn.
    Context {TE : Type}.

    Inductive t : Type := empty : t.

    Inductive EmptyGenStep : t -> option (t * TE) -> Prop :=
      empty_step : EmptyGenStep empty None.

    Global Instance emptyGen : Generator TE t :=
      { gen_step := EmptyGenStep }.
  End defn.

  Lemma empty_generator : forall TE (l : list TE),
      GenEnsemble empty l ->
      l = [].
  Proof.
    intros.
    inversion H.
    - easy.
    - simpl in H0. inversion H0.
  Qed.
End Empty.

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

    Inductive ThreadGenStep : t -> option (t * TE) -> Prop :=
    | tstep_nil :
        ThreadGenStep p_dead None
    | tstep_cons : forall (req : Request) cont (rep : Reply req),
        ThreadGenStep (p_cont req cont)
                      (Some (cont rep, rep <~ req)).

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

    Local Ltac inv a := inversion a; subst; clear a.

    Goal forall t,
        GenEnsemble my_prog t ->
        exists x y z,
          t = [0 <~ true; x <~ false] \/
          t = [y <~ true; z <~ true].
    Proof.
      intros. subst my_prog.
      inv H.
      - exfalso. inv H0.
      - inv H0.
    Abort.
  End tests.
End process.

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

  Definition wrap_singleton : list TE -> list (ProcessEvent TE) :=
    map (fun e => 0 @ e).
End parallel_defn.

Infix "<||>" := parallel (right associativity, at level 101) : slot_scope.
Notation "[| |]" := (Empty.t) : slot_scope.
Notation "[| x |]" := (wrap_singleton x) : slot_scope.
Notation "[| x ; .. ; y ; z |]" := (parallel x (.. (parallel y (wrap_singleton z)) ..)) : slot_scope.

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

Section gen_commutativity.
  Context {TE Gen} `{Generator (ProcessEvent TE) Gen}.

  Definition generator_events_commute g te1 te2 g' :=
    (exists g0,
        g  ~~> g0 & te1 /\ g0 ~~> g' & te2) ->
    exists g1,
      g' ~~> g1 & te2 \/ g1 ~~> g & te1.
End gen_commutativity.

(* Lemma gen_pair_comm {G1 G2 TE} `{Generator TE G1} `{Generator TE G2} (g1 : G1) (g2 : G2) (te1 te2 : TE) (p1 p2 : PID) : *)
(*   p1 <> p2 -> *)
(*   generator_events_commute (g1 <||> g2) (p1 @ te1) (p2 @ te2). *)
(* Proof. *)
(*   unfold generator_events_commute. intros *. intros Hpids Hg' Hg''. *)
(*   inversion Hg'; subst. *)
(*   - *)

Section optimize.
  Context {Gen State Event : Type}.
  Let TE := (ProcessEvent Event).
  Context `{Hssp : StateSpace State TE} `{Hgen : Generator TE Gen}.

  Let can_follow (te1 te2 : TE) : Prop :=
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

  Lemma not_leq : (forall a b, not (a <= b) -> b <= a).
  Proof.
    sauto.
  Qed.

  Fixpoint gen_ens_opt (g : Gen) (t : list TE) (Ht : GenEnsemble g t) {struct t} :
    exists t' : list TE, GenEnsembleOpt g t' /\ Permutation events_commute t t'.
  Proof with auto with slot.
    destruct Ht.
    - exists []. split; now constructor.
    - specialize (gen_ens_opt _ _ Ht). destruct gen_ens_opt as [t' [Ht' Hperm]].
      destruct t' as [ | te' t'].
      + exists [te].
        apply perm_empty in Hperm; subst.
        split.
        * inversion Ht. constructor 2 with g'...
        * repeat constructor.
      + destruct te as [pid te]. destruct te' as [pid' te'].
        destruct (classic (pid <= pid')).
        * exists (pid @ te :: pid' @ te' :: t'). split.
          -- constructor 3 with g'...
             ++ now left.
          -- constructor. constructor 4 with t...
        * destruct (classic (events_commute (pid @ te) (pid' @ te'))).
          -- exists (pid' @ te' :: pid @ te :: t'). split.
             2:{ constructor 4 with (pid @ te :: pid' @ te' :: t').
                 - now constructor.
                 - now constructor.
             }
             constructor 3 with g'.
             2:{ left. now apply not_leq in H0. }
  Admitted.

  Theorem optimize_gen_p g :
    sufficient_replacement_p (GenEnsemble g) (GenEnsembleOpt g).
  Proof.
    intros t Ht.
    now apply gen_ens_opt.
  Qed.

  Theorem optimize_gen (g : Gen) P Q :
    -{{ P }} GenEnsembleOpt g {{ Q }} ->
    -{{ P }} GenEnsemble g {{ Q }}.
  Proof.
    apply ht_sufficient_replacement, comm_perm_sufficient_replacement, optimize_gen_p.
  Qed.
End optimize.

Require Handlers.Deterministic.

Section optimize_tests.
  Import Deterministic.Var.

  Let e (a : PID) (b : nat) : TraceElem var_req_t var_ret_t := a @ I <~ write b.

  Goal forall t,
      GenEnsembleOpt [| [I <~ write 3] ; [I <~ write 1; I <~ write 2] |] t ->
      t = [1 @ I <~ write 1; 1 @ I <~ write 2; 0 @ I <~ write 3] \/
      t = [1 @ I <~ write 1; 0 @ I <~ write 3; 1 @ I <~ write 2] \/
      t = [0 @ I <~ write 3; 1 @ I <~ write 1; 1 @ I <~ write 2].
  Proof.
    intros. sauto.
  Qed.

  Hint Resolve var_ww_comm:slot.

  (* Check that it creates every interleaving: *)
  Goal GenEnsembleOpt [| [I <~ write 1; I <~ write 2]; [I <~ write 3] |]
       [e 0 1; e 0 2; e 1 3].
  Proof.
    sauto db:slot.
  Qed.

  Goal GenEnsembleOpt [| [I <~ write 1; I <~ write 2]; [I <~ write 3] |]
       [e 0 1; e 1 3; e 0 2].
  Proof.
    sauto use:var_ww_comm.
    constructor 3 with (g' := [| [I <~ write 2]; [I <~ write 3] |]); try sauto.
    - constructor 3 with (g' := [| [I <~ write 2]; [] |]); try sauto.
      constructor 2; try sauto.
      intros s s'.
  Qed.


  Goal GenEnsembleOpt [| [1; 2] ; [3] |] [1 @ 3; 0 @ 1; 0 @ 2].
  Proof.
    constructor 3 with (g' := [| [1; 2] ; [] |]).
    - sauto.
    - constructor 3 with (g' := [| [2] ; [] |]); sauto.
  Qed.
End optimize_tests.
