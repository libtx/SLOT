(* SLOT, proofs about distributed systems design
   Copyright (C) 2019-2023  k32

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
From Coq Require Import
     List
     Relations.

Import ListNotations.

From SLOT Require Export
     Foundations
     Permutation
     Commutativity
     Tactics.

Section defns.
  Context `{Hssp : StateSpace}.

  (** [rbt_split] is an important observation that there is a point in
  the state space for each intermediate step of the trace
  execution: *)
  Lemma rbt_split : forall s s'' t1 t2,
      ReachableByTrace s (t1 ++ t2) s'' ->
      exists s', ReachableByTrace s t1 s' /\ ReachableByTrace s' t2 s''.
  Proof.
    intros.
    generalize dependent s.
    induction t1; intros.
    - exists s.
      split; auto with slot.
    - long_step H.
      specialize (IHt1 s0 H).
      destruct IHt1.
      exists x. split.
      + forward s0; firstorder.
      + firstorder.
  Qed.

  (** [rbt_concat] lemma demonstrates that traces can be composed: *)
  Lemma rbt_concat : forall s s' s'' t1 t2,
      ReachableByTrace s t1 s' ->
      ReachableByTrace s' t2 s'' ->
      ReachableByTrace s (t1 ++ t2) s''.
  Proof with auto.
    intros.
    generalize dependent s.
    induction t1; intros; simpl...
    - inversion H...
    - long_step H.
      forward s0...
  Qed.

  Lemma ht_comm_perm  s s' t t' :
    ReachableByTrace s t s' ->
    Permutation events_commute t t' ->
    ReachableByTrace s t' s'.
  Proof with eauto with slot.
    intros Hls Hperm.
    generalize dependent s.
    induction Hperm; intros...
    - long_step Hls.
      forward s0...
    - unfold_trace Hls.
      specialize (H s s1).
      replace (b :: a :: l) with ([b; a] ++ l) by reflexivity.
      apply rbt_concat with (s' := s1)...
      apply H.
      forward s0...
  Qed.
End defns.

Section ensemble_equiv.
  Context `{StateSpace} (e1 e2 : TraceEnsemble Event).

  Definition sufficient_replacement :=
    forall t s s', e1 t ->
              ReachableByTrace s t s' ->
              exists t', e2 t' /\ ReachableByTrace s t' s'.

  Definition sufficient_replacement_p :=
    forall t, e1 t ->
         exists t', e2 t' /\ Permutation events_commute t t'.

  Theorem ht_sufficient_replacement P Q :
    sufficient_replacement ->
    -{{P}} e2 {{Q}} -> -{{P}} e1 {{Q}}.
  Proof.
    intros He2 Heht t Ht s s' Hls Hpre.
    destruct (He2 t s s' Ht Hls) as [t' [Ht' Hls']].
    eapply Heht; eauto.
  Qed.

  Lemma comm_perm_sufficient_replacement :
    sufficient_replacement_p ->
    sufficient_replacement.
  Proof.
    intros Hsrp t s s' Ht Hls.
    destruct (Hsrp t Ht) as [t' [Ht' Hperm]].
    eapply ht_comm_perm in Hperm; eauto.
  Qed.
End ensemble_equiv.

Lemma sufficient_replacement_p_trans `{StateSpace} :
  transitive (@TraceEnsemble Event) sufficient_replacement_p.
Proof.
  intros e1 e2 e3 H12 H23. intros t Ht.
  apply H12 in Ht. destruct Ht as [t' [Ht' Hperm']].
  apply H23 in Ht'. destruct Ht' as [t'' [Ht'' Hperm'']].
  exists t''. split.
  - assumption.
  - eapply perm_trans; eauto.
Qed.
