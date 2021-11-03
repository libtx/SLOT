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
     Foundations.

From Hammer Require Import
     Tactics.

Class Generator TE g :=
  { gen_step : g -> option (g * TE) -> Prop
  }.

Notation "A '~~>' B & C" := (gen_step A (Some (B, C))) (at level 20).

Notation "A '~~>x'" := (gen_step A None) (at level 20).

Section GenEnsemble.
  (** Generator from an ensemble *)
  Context {TE G : Type} `{Generator TE G}.

  Inductive GenEnsemble (g : G) : @TraceEnsemble TE :=
  | gen_ens_nil :
      gen_step g None ->
      GenEnsemble g []
  | gen_ens_cons : forall g' te t,
      gen_step g (Some (g', te)) ->
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

Module List.
  Section defn.
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
  End defn.
End List.

Module Process.
  Section defn.
    Context {Request : Type} {Reply : Request -> Type}.

    Let TE := IOp Request Reply.
    Let t := @Program Request Reply.

    Inductive ThreadGenStep : t -> option (t * TE) -> Prop :=
    | tstep_nil :
        ThreadGenStep p_dead None
    | tstep_cons : forall req cont (rep : Reply req),
        ThreadGenStep (p_cont req cont)
                      (Some (cont rep, rep <~ req)).

    Global Instance processGen : Generator TE t :=
    { gen_step := ThreadGenStep }.
  End defn.

  (* Section tests. *)
  (*   Import . *)

  (*   Let PID := True. *)
  (*   Let Handler := @Var.t PID nat. *)
  (*   Let Req := get_handler_req_pid Handler. *)
  (*   Let Rep := get_handler_ret_pid Handler. *)
  (*   Let TE := @TraceElem PID Req Rep. *)

  (*   Let my_prog : @Process _ Req Rep I := *)
  (*     spawn I (do x <- Var.read; *)
  (*              match x with *)
  (*              | 0 => *)
  (*                done Var.write 3 *)
  (*              | _ => *)
  (*                done Var.write 0 *)
  (*              end). *)

  (*   Local Ltac inv a := inversion a; subst; clear a. *)

  (*   Goal forall t, *)
  (*       GenEnsemble my_prog t -> *)
  (*       exists x, *)
  (*         t = [I @ 0 <~ Var.read; I @ I <~ Var.write 3] \/ *)
  (*         t = [I @ x <~ Var.read; I @ I <~ Var.write 1]. *)
  (*   Proof. *)
  (*     intros. subst my_prog. *)
  (*     inv H. *)
  (*     - exfalso. inv H0. *)
  (*     - inv H0. *)
  (*   Abort. *)
  (* End tests. *)
End Process.

Module Parallel.
  Section defn.
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
  End defn.

  Infix "<||>" := parallel (right associativity, at level 101) : slot_scope.
  Notation "[| |]" := (Empty.t) : slot_scope.
  Notation "[| x |]" := (wrap_singleton x) : slot_scope.
  Notation "[| x ; .. ; y ; z |]" := (parallel x (.. (parallel y (wrap_singleton z)) ..)) : slot_scope.

  Section tests.
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
  End tests.
End Parallel.
