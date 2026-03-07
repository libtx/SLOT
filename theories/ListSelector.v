From Coq Require Import
  List.

Import ListNotations.

From Hammer Require Import
  Tactics.

Require Import Setoids.

Open Scope slot_scope.

Section defn.
  Context {A : Type}.

  Definition Pick (l : list A) a (l' : list A) : Prop :=
    Add a l' l.

  (* Lemma permutation_split (a : A) l1 l2 : *)
  (*   (a :: l1) =p= l2 -> *)
  (*   exists l3 l4, *)
  (*     l2 = (l3 ++ a :: l4). *)
  (* Admitted. *)

  Lemma pick_equiv l1 l1' l2 a :
    l1 =p= l1' ->
    Pick l1 a l2 ->
    exists l2',
      Pick l1' a l2' /\ l2 =p= l2'.
  (* Proof. *)
  (*   unfold Pick. intros Hl1 Hl2. *)
  (*   generalize dependent l1'. *)

  (*   induction Hl2; intros l1' Hl1. *)
  (*   - apply Permutation_in with (x := a) in Hl1 as Hl1'. *)
  (*     + destruct (Add_inv a l1' Hl1') as [l2' Hl2']. *)
  (*       exists l2'. split. *)
  (*       * assumption. *)
  (*       * apply Permutation_Add in Hl2'. *)
  (*         rewrite <-Hl1 in Hl2'. *)
  (*         now apply Permutation_cons_inv in Hl2'. *)
  (*     + now constructor. *)
  (*   - apply permutation_split in Hl1 as H. *)
  (*     destruct H as [l3 [l4 Hl34]]. subst. *)
  (*     rewrite <-Permutation_middle in Hl1. apply Permutation_cons_inv in Hl1. *)
  (*     specialize (IHHl2 (l3 ++ l4) Hl1). *)
  (*     destruct IHHl2 as [l5 [Hl5 Hll5]]. *)
  (*     exists (x :: ). *)
  (*     split. *)
  (*     +  *)
  (*     exists (l3 ++ l4). *)





  (*     Search Permutation. *)
  (*   induction Hl2. *)
  (*   - apply Permutation_Add in Hl1. *)
  (*   apply Permutation_Add in Hl2 as H. rewrite Hl1 in H. clear Hl1. *)

  (*   induction Hl1. *)
  (*   2:{  *)


  (*   apply Add_split in Hl2. *)
  (*   destruct Hl2 as [l3 [l4 [Hl3 Hl4]]]. subst. *)
  (*   Check Permutation_Add. *)

  (*   induction l1'. *)
  (*   - exfalso. inversion Hl1. *)
  (*     now apply Permutation_sym, Permutation_nil_cons in Hl1. *)
  (*   -  *)
  (*   Check Permutation_cons_app. *)

  (*   rewrite Permutation_middle in Hl1. *)
  (*   Search Permutation. *)
  (*   apply Permutation_cons_inv in H. *)


  (*   replace (a :: l2) with ([] ++ a :: l2) in Hl1 by now rewrite <-app_nil_l. *)
  (*   rewrite <-Permutation_middle in Hl1. *)
  (*   Search Add. *)

  (* (*   intros Hl1 Hl2. *) *)
  (*   apply pick_via_app in Hl2 as H. destruct H as [l3 [l4 Hl34]]. subst. *)
  (*   rewrite <-Permutation_middle in Hl1. *)
  (*   apply pick_via_permutation2 in Hl1 as Hl5. *)
  (*   destruct Hl5 as [l5 Hl5]. *)
  (*   exists l5. *)
  (*   split. *)
  (*   - assumption. *)
  (*   - apply pick_via_permutation in Hl5. *)
  (*     apply pick_via_permutation in Hl2. *)
  (*     rewrite <-Permutation_middle in Hl2. *)
  (*     apply Permutation_cons_inv in Hl2. *)
  (*     rewrite Hl2. rewrite <-Hl1 in Hl5. *)
  (*     now apply Permutation_cons_inv, Permutation_sym in Hl5. *)
    (* Qed. *)
  Admitted.
End defn.

Section tests.
  Goal forall a l',
      Pick [1; 2; 3] a l' ->
        (a = 1 /\ l' = [2; 3]) \/
        (a = 2 /\ l' = [1; 3]) \/
        (a = 3 /\ l' = [1; 2]).
  Proof.
    sauto.
  Qed.
End tests.
