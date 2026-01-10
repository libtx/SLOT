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
     Relations
     SetoidClass.

From Hammer Require Import
     Tactics.

Import ListNotations.

Section defn.
  Context {T : Type} (can_swap : T -> T -> Prop).
  Let L := list T.

  Inductive RestrictedPermutation : L -> L -> Prop :=
  | perm_nil :
      RestrictedPermutation [] []
  | perm_cons : forall a l1 l2,
      RestrictedPermutation l1 l2 ->
      RestrictedPermutation (a :: l1) (a :: l2)
  | perm_swap : forall a b l,
      can_swap a b ->
      RestrictedPermutation (a :: b :: l) (b :: a :: l)
  | perm_trans : forall l l' l'',
      RestrictedPermutation l l' ->
      RestrictedPermutation l' l'' ->
      RestrictedPermutation l l''.

  Lemma perm_refl t : RestrictedPermutation t t.
  Proof.
    induction t; now constructor.
  Qed.

  Lemma perm_empty_r a : RestrictedPermutation a [] -> a = [].
  Proof.
    intros H.
    remember [] as b eqn:Hb.
    induction H; subst; try now inversion Hb.
    - rewrite IHRestrictedPermutation1, IHRestrictedPermutation2; auto.
  Qed.

  Lemma perm_empty_l a : RestrictedPermutation [] a -> a = [].
  Proof.
    intros H.
    remember [] as b eqn:Hb.
    induction H; subst; try now inversion Hb.
    - rewrite IHRestrictedPermutation2, IHRestrictedPermutation1; auto.
  Qed.

  Lemma perm_symm (Hsymm : Symmetric can_swap): Symmetric RestrictedPermutation.
  Proof.
    intros a b H.
    induction H.
    - constructor.
    - now constructor.
    - constructor. now apply Hsymm.
    - constructor 4 with (l' := l'); assumption.
  Qed.
End defn.

#[export] Hint Constructors RestrictedPermutation : slot.
#[export] Hint Resolve perm_refl perm_empty_r perm_empty_l : slot.
