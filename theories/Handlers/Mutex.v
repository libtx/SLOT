(* SLOT, a formally verified model checker
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
     List.

Import ListNotations.

From SLOT Require Import
     Foundations
     Properties
     Tactics.

Section defs.
  Open Scope slot_scope.

  Inductive req_t : Set :=
  | grab    : req_t
  | release : req_t.

  Local Definition ret_t (req : req_t) : Set :=
    match req with
    | grab => True
    | release => bool
    end.

  Definition state_t := option PID.

  Let TE := TraceElem req_t ret_t.

  Inductive mutex_state_transition : state_t -> TE -> state_t -> Prop :=
  | mutex_grab : forall pid,
      mutex_state_transition None (pid @ I <~ grab) (Some pid)
  | mutex_release_ok : forall pid,
      mutex_state_transition (Some pid) (pid @ true <~ release) None
  | mutex_release_fail : forall pid,
      mutex_state_transition None (pid @ false <~ release) None.

  Global Instance t : @IOHandler req_t ret_t :=
    { h_state := state_t;
      h_state_transition := mutex_state_transition;
    }.

  Theorem no_double_grab : forall (a1 a2 : PID),
      {{ fun _  => True }}
        [a1 @ I <~ grab;
         a2 @ I <~ grab]
      {{ fun _ => False }}.
  Proof.
    intros a1 a2 s s' Hss' Hpre.
    unfold_trace_deep Hss'.
    discriminate.
  Qed.

  Theorem no_double_grab_0 : forall (a1 a2 : PID),
      ~(PossibleTrace [a1 @ I <~ grab;
                       a2 @ I <~ grab]).
  Proof.
    intros a1 a2 H.
    destruct H as [s [s' H]].
    unfold_trace_deep H.
    discriminate.
  Qed.
End defs.

Ltac mutex_contradiction :=
  match goal with
    [H1 : mutex_state_transition _ ?s1 ?s2 _, H2 : mutex_state_transition _ ?s2 ?s3 _ |- _] =>
      inversion H1; inversion H2; subst; discriminate
  end.

#[export] Hint Extern 4 => mutex_contradiction : handlers.

Ltac clear_mutex :=
  repeat match goal with
           [H: mutex_state_transition _ _ _ _ |- _] => clear H
         end.
