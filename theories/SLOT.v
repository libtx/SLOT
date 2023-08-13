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
     Handlers
     Bruteforce.

From Coq Require Import List.
Import ListNotations.

(* begin: hide *)
Require Handlers.Deterministic
        Handlers.Mutex.
(* end: hide *)

From Ltac2 Require Import Ltac2 Std Init.
Set Default Proof Mode "Ltac2".

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
  Definition TE := ProcessEvent (@IOp Req Rep).

  Definition prog : @Program Req Rep :=
    do _ <- req mutex grab;
    do x <- req var read;
    do _ <- req var (write (x + 1));
    done (req mutex release).

  Import better_parallel.

  Definition system := of_progs [prog; prog].

  Goal forall n,
      -{{ fun s => stateG s var = n }}
         GenEnsembleOpt system
       {{ fun s => stateG s var = n + 2 }}.
  Proof with auto with slot.
    intros n t Hg [s_begin1 s_begin2] [s_end1 s_end2] Hrbt Hpre.
    unfold stateG in *. simpl in *.
    unfold Ensembles.In, system, of_progs in Hg.
    gen_par_unfold @t @Hg
      (fun _ => match handler_step @Hrbt with
             | None => ()
             | Some (te, s, hcr) =>
                 (* destruct s; *)
                 (* unfold compose_state_transition in hcr; *)
                 (* (* printf "%t" (type (hyp hcr)); *) *)
                 (* (* ifcatch (fun () => split_all_clauses hcr) (fun _  => ()) (fun f => Message.print (Message.of_exn f)) *) *)
                 (* split_all_clauses hcr; *)
                 (* lazy_match! goal with *)
                 (* | [ h : mutex_state_transition _ _ _  |- _] => *)
                 (*     let h := hyp h in *)
                 (*     inversion $h *)
                 (* end *)
                 ()
             end).
    - ltac1:(lia).
    - ltac1:(lia).
  Qed.
End Example.
