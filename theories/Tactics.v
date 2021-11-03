(* SLOT, proofs about distributed systems design
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
From Coq Require Import
     List.

Import ListNotations.

From SLOT Require Import
     Foundations.

Open Scope slot_scope.

Ltac long_step f tac :=
  cbn in f;
  lazymatch type of f with
  | ReachableByTrace _ [] _ =>
    let s := fresh "s" in
    let Hx := fresh "Hx" in
    let Hy := fresh "Hy" in
    let Hz := fresh "Hz" in
    inversion f as [s Hx Hy Hz|];
    subst s; clear f; clear Hy
  | ReachableByTrace _ (_ :: _) _ =>
    let s' := fresh "s" in
    let te := fresh "te" in
    let tail := fresh "tail" in
    let Hcr := fresh "Hcr" in
    let Htl := fresh "Htl" in
    inversion_clear f as [|? s' ? te tail Hcr Htl];
    rename Htl into f;
    cbn in Hcr;
    tac Hcr
  end.

Tactic Notation "long_step" ident(f) tactic3(tac) := long_step f tac.
Tactic Notation "long_step" ident(f) := long_step f (fun _ => idtac).

Ltac unfold_trace f tac :=
  repeat (long_step f tac).

Tactic Notation "unfold_trace" ident(f) tactic3(tac) := unfold_trace f tac.
Tactic Notation "unfold_trace" ident(f) := unfold_trace f (fun _ => idtac).
Tactic Notation "unfold_trace_deep" ident(f) := unfold_trace f (fun x => inversion x); subst.

Ltac ls_advance tac :=
  match goal with
  | [H : ReachableByTrace ?s ?t ?s' |- ?Q ?s'] =>
    long_step H tac
  end.

Tactic Notation "ls_advance" tactic3(tac) := ls_advance tac.
Tactic Notation "ls_advance" := ls_advance (fun _ => idtac).

Hint Transparent Ensembles.In Ensembles.Complement : slot.
Hint Constructors ReachableByTrace : slot.
(* Hint Resolve trace_elems_commute_symm : slot. *)

Ltac unfold_ht :=
  match goal with
  | [ |- {{?pre}} ?t {{?post}}] =>
    let s := fresh "s_begin" in
    let s' := fresh "s_end" in
    let Hls := fresh "Hls" in
    let Hpre := fresh "Hpre" in
    intros s s' Hls Hpre;
    match eval cbn in Hpre with
    | [fun _ => True] => clear Hpre (* TODO: Fixme *)
    | _ => idtac
    end
  | _ =>
    fail "Goal does not look like a Hoare triple"
  end.
