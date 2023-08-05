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
    (H : Ensembles.In (GenEnsembleOpt {| last_pid := last_pid; processes := []|}) t) :
    t = [].
  Proof.
    inversion H.
    - reflexivity.
    - inversion H0.
    - inversion H0.
  Qed.

  Lemma canned_par_opt_two {last_pid p1 p2 rest}
    {t : Trace Req Rep}
    (H : Ensembles.In (GenEnsembleOpt {| last_pid := last_pid; processes := p1 :: p2 :: rest|}) t) :
    exists pid1 req rep,
      t = [pid1 @ rep <~ req].
  Admitted.

  Goal forall n,
      -{{ fun s => stateG s var = n }} GenEnsembleOpt system {{ fun s => stateG s var = n + 2 }}.
  Proof with auto with slot.
    intros n.
    unfold_ht.
    unfold system, better_parallel.of_progs in Ht.
    inversion Ht.
    3:{ inversion Ht.
        3:{
      apply canned_par_opt_two in Ht.
    specialize (canned_par_opt_two Ht) as H.


    cbn in Ht.
    inversion Ht.
    - exfalso. simpl in H. firstorder; discriminate.
    - simpl in H. firstorder.

    apply parallel_processes_ht...
    unfold_ht. inversion Ht.
  Abort.
End Example.
