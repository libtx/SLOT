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

(** * Commutativity of trace elements *)
From Coq Require Import
     List
     Program
     Logic.Classical_Prop
     Logic.Decidable
     Classes.RelationClasses.

Import ListNotations.

From SLOT Require Import
     Foundations.

Section events_commute.
  (** ** Commutativity of trace elements
   *)
  Context `{StateSpace}.

  Definition events_commute (e1 e2 : Event) :=
    forall (s s' : State),
      ReachableByTrace s [e1; e2] s' <-> ReachableByTrace s [e2; e1] s'.

  Global Instance events_commuteSymm : Symmetric events_commute.
  Proof.
    intros a b Hab s s''.
    unfold events_commute in *. specialize (Hab s s'').
    now symmetry in Hab.
  Qed.
End events_commute.
