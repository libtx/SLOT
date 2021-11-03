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
     Relations.

Import ListNotations.

From SLOT Require Import
     Foundations.

Class CommRel {A} :=
  { comm_rel : relation A;
    comm_rel_symm : symmetric _ comm_rel;
    comm_rel_dec : forall a b, decidable (comm_rel a b);
  }.

Global Arguments CommRel : clear implicits.

Section events_commute.
  (** ** Commutativity of trace elements
   *)
  Context `{StateSpace}.

  Definition events_commute (e1 e2 : Event) :=
    forall (s s' : State),
      ReachableByTrace s [e1; e2] s' <-> ReachableByTrace s [e2; e1] s'.

  Lemma events_commute_dec `{StateSpace} a b : decidable (events_commute a b).
  Proof.
    apply classic.
  Qed.

  Program Instance eventCommRel : CommRel Event :=
    { comm_rel a b := events_commute a b
    }.
  Next Obligation.
    unfold symmetric. intros x y Hcomm.
    firstorder. Qed.
  Next Obligation.
    apply events_commute_dec.
  Qed.
End events_commute.

Section never_comm_rel.
  Program Instance neverCommRel {T} : CommRel T :=
    { comm_rel := fun _ _ => False;
    }.
  Next Obligation.
    easy. Qed.
  Next Obligation.
    apply classic.
  Qed.
End never_comm_rel.

Module Test.
  Inductive T :=
  | r : nat -> T
  | w : nat -> T.

  Definition test_comm_rel (a b : T) : Prop :=
    match a, b with
    | r _, r _ => True
    | _  , _   => False
    end.

  Program Instance parityCommRel : CommRel T :=
    { comm_rel := test_comm_rel
    }.
  Next Obligation.
    unfold test_comm_rel, symmetric.
    destruct x; destruct y; auto.
  Qed.
  Next Obligation.
    unfold test_comm_rel, decidable.
    destruct a; destruct b; auto.
  Qed.
End Test.
