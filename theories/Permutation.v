(* SLOT, a formally verified model-checker

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

(** Almost an exact copy of [Permutation] definition from the Coq
standard library, but with an additional predicate that specifies
whether the elements can be swapped *)
From Coq Require Import
     List
     Tactics
     Arith.Even
     Relations.

From Hammer Require Import
     Tactics.

Import ListNotations.

Section defn.
  Context {T : Type} (can_swap : T -> T -> Prop).
  Let L := list T.

  Inductive Permutation : L -> L -> Prop :=
  | perm_nil :
      Permutation [] []
  | perm_cons : forall a l1 l2,
      Permutation l1 l2 ->
      Permutation (a :: l1) (a :: l2)
  | perm_swap : forall a b l,
      can_swap a b ->
      Permutation (a :: b :: l) (b :: a :: l)
  | perm_trans : forall l l' l'',
      Permutation l l' ->
      Permutation l' l'' ->
      Permutation l l''.

  Lemma perm_empty a : Permutation a [] -> a = [].
  Proof.
    intros H.
    remember [] as b eqn:Hb.
    induction H; subst; try now inversion Hb.
    - rewrite IHPermutation1, IHPermutation2; auto.
  Qed.

  Lemma perm_refl t : Permutation t t.
  Proof.
    induction t; now constructor.
  Qed.
End defn.

Hint Constructors Permutation : slot.
Hint Resolve perm_refl : slot.
Hint Resolve perm_empty : slot.
