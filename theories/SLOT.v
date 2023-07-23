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

  Definition Req := handler_request_t handler.
  Definition Rep := handler_reply_t handler.

  Definition prog : @Program Req Rep :=
    do _ <- req mutex grab;
    do x <- req var read;
    do _ <- req var (write (x + 1));
    done (req mutex release).

  Definition system := [| prog; prog |].

  (* Goal forall n, *)
  (*     -{{ fun s => val s = n }} GenEnsemble system {{ fun s => val s = n + 2 }}. *)
  (* Proof with auto with slot. *)
  (*   intros n. *)
  (*   apply parallel_processes_ht... *)
  (*   unfold_ht. inversion Ht. *)
  (* Abort. *)
End Example.
