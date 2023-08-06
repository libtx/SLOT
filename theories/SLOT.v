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
     Tactics
     Handlers.

From Hammer Require Import
     Tactics.

From Coq Require Import List.
Import ListNotations.

(* begin: hide *)
Require Handlers.Deterministic
        Handlers.Mutex.
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

  Ltac clauses H :=
    lazymatch type of H with
    | ?A \/ ?B => destruct H as [H|H]; [idtac|clauses H]
    | _ => idtac
    end.

  Ltac gen_par_unfold H :=
    let g' := fresh "g" in
    let te := fresh "te" in
    let t' := fresh "t'" in
    let Ht := fresh "Ht" in
    let Ht' := fresh "Ht'" in
    let Htete' := fresh "Htete'" in
    let Hg' := fresh "Hg'" in
    apply canned_par_opt_two in H;
    destruct H as [g' [te [t' [Ht [Ht' [Htete' Hg']]]]]];
    cbn in Ht';
    clauses Ht';
    let rep := fresh "rep" in
    destruct Ht' as [rep Ht'];
    inversion Ht'; subst; clear Ht'.

  Ltac gen_step :=
    lazymatch goal with
    | [ H : GenEnsembleOpt {| processes := [] |} ?t |- _] =>
        apply canned_par_opt_nil in H; subst t
    | [ H : GenEnsembleOpt {| processes := ?pp |} ?t |- _] =>
        gen_par_unfold H
    end.

  Goal forall n,
      -{{ fun s => stateG s var = n }} GenEnsembleOpt system {{ fun s => stateG s var = n + 2 }}.
  Proof with auto with slot.
    intros n.
    unfold_ht.
    unfold Ensembles.In, system, better_parallel.of_progs in Ht.
    repeat gen_step.
  Abort.
End Example.
