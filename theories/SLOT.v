(* SLOT, a formally verified model checker
   Copyright (C) 2021-2023  k32

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

From SLOT Require Export
     Foundations
     Generator
     Commutativity
     Handlers.

From Hammer Require Import
     Tactics.

From Coq Require Import List.
Import ListNotations.

(* begin: hide *)
Require Handlers.Deterministic
        Handlers.Mutex.

From Ltac2 Require Import Init List Ind Env Control Option Constr Std Array Notations Fresh Printf.
(* end: hide *)

Module Example.
  Import Handlers.Deterministic Handlers.Deterministic.Var Mutex.

  Inductive handlerId := var | mutex.

  Ltac2 handlerSpec () := ['(Var.t nat); 'Mutex.t].

  Definition handler := ltac2:(makeClass handlerSpec).
  Definition reqT := ltac2:(makeRequestType handlerSpec 'handlerId).
  Definition req := ltac2:(makeReq handlerSpec 'handlerId 'reqT 'handler).
  Definition stateG := ltac2:(makeStateGetter handlerSpec 'handler 'handlerId).

  Definition Req := handler_request_t handler.
  Definition Rep := handler_reply_t handler.

  Definition prog : @Program Req Rep :=
    do _ <- req mutex grab;
    do x <- req var read;
    do _ <- req var (write (x + 1));
    done (req mutex release).

  Import better_parallel.

  Definition system := of_progs [prog; prog].

  Lemma canned_par_opt_nil {last_pid}
    {t : Trace Req Rep}
    (H : GenEnsembleOpt {| last_pid := last_pid; processes := []|} t) :
    t = [].
  Proof.
    inversion H.
    - reflexivity.
    - inversion H0.
  Qed.

  Lemma canned_par_opt_two {last_pid p rest}
    {t : Trace Req Rep}
    (H : GenEnsembleOpt {| last_pid := last_pid; processes := p :: rest|} t) :
    exists g' te t',
      t = te :: t' /\
      {| last_pid := last_pid; processes := p :: rest|} ~~> g' & te /\
        can_follow_hd te t' /\
        GenEnsembleOpt g' t'.
  Admitted.

Section tests.

  (* Ltac clauses H := *)
  (*   lazymatch type of H with *)
  (*   | ?A \/ ?B => destruct H as [H|H]; [idtac|clauses H] *)
  (*   | _ => idtac *)
  (*   end. *)

  Ltac2 rec split_all_clauses (n : ident) :=
    let h := hyp n in
    let t := Constr.type h in
    lazy_match! t with
    | ?a \/ ?b => destruct $h as [$n | $n] > [() | split_all_clauses n]
    | _ => ()
    end.

  (* Test: *)
  Goal True \/ True \/ True \/ True -> False.
    intros H.
    split_all_clauses @H > [() | () | () | ()].
  Abort.

  Ltac2 simpl_par_cons_rep (n : ident) (g : ident) (te : ident) :=
    let rep := in_goal @rep in
    let h := hyp n in
    destruct $h as [$rep $n];
    let h := hyp n in
    let hte := in_goal @Hte in
    injection $h as $n $hte;
    subst $g;
    subst $te.

  (* Test: *)
  Goal forall g te,
      (exists rep : True, Some (g, te) = Some (1, 2)) ->
      g = 1 /\ te = 2.
    intros g te H.
    simpl_par_cons_rep @H @g @te.
    split; reflexivity.
  Qed.

  Ltac2 Type prev_hyps := {comm_hyp : ident; te : ident}.

  Ltac2 gen_par_cons_unfold (prev : prev_hyps option) (t : ident) (n : ident) cont :=
    let g' := in_goal @g in
    let te := in_goal @te in
    let t' := in_goal @t' in
    let ht := in_goal @Ht in
    let htete' := in_goal @Htete' in
    let hg' := in_goal @Hg' in
    apply canned_par_opt_two in $n;
    let h := hyp n in
    destruct $h as [$g' [$te [$t' [$ht [$n [$htete' $hg']]]]]];
    subst $t;
    cbn in $n;
    split_all_clauses n >
      [simpl_par_cons_rep n g' te;
       cont t' hg'..].

  Ltac2 rec gen_par_unfold (t : ident) (n : ident) :=
    lazy_match! type (hyp n) with
    | GenEnsembleOpt {| processes := [] |} _ =>
        apply canned_par_opt_nil in $n ; subst $t
    | GenEnsembleOpt {| processes := ?pp |} _ =>
        gen_par_cons_unfold t n (gen_par_unfold check_state)
    end.

  Ltac2 check_commut () :=
    match! goal with
    | [ h : can_follow_hd ?a [] |- _] =>
        clear $h
    | [ h : can_follow_hd ?te1 (?te2 :: _) |- _] =>
        printf "found: %I %t %t" h te1 te2;
        clear $h
    end.

  Goal forall n,
      -{{ fun s => stateG s var = n }} GenEnsembleOpt system {{ fun s => stateG s var = n + 2 }}.
  Proof with auto with slot.
    intros n t Hg s_begin s_end Hrbt Hpre.
    unfold Ensembles.In, system, of_progs in Hg.
    gen_par_unfold () @t @Hg.
    repeat (check_commut ()).
    check_commut ().
  Abort.
End Example.
