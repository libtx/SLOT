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
  Import Handlers.Deterministic.

  Definition handler := Var.t nat <+> Mutex.t.

  Definition Req := handler_request_t handler.
  Definition Rep := handler_reply_t handler.
  Definition State := @h_state _ _ handler.

  Definition write (val : nat) : Req.
    lift (Var.write val).
  Defined.

  Definition read : Req.
    lift (@Var.read nat).
  Defined.

  Definition grab : Req.
    lift Mutex.grab.
  Defined.

  Definition release : Req.
    lift Mutex.release.
  Defined.

  Definition val (s : State) : nat.
    cbv in s. destruct s.
    exact n.
  Defined.

  Definition prog : @Program Req Rep :=
    do _ <- grab;
    do x <- read;
    do _ <- write (S x);
    done release.

  Definition system := [| prog; prog |].

  Goal forall n,
      -{{ fun s => val s = n }} GenEnsemble system {{ fun s => val s = n + 2 }}.
  Proof with auto with slot.
    intros n.
    apply parallel_processes_ht...
    unfold_ht. inversion Ht.
  Abort.
End Example.
