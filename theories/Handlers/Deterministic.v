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

(** * Generic total deterministic IO handler *)
From Coq Require Import
     List.

From LibTx Require
     Storage.

(* From Coq Require *)
(*      ZArith.BinInt *)
(*      FSets.FMapAVL. *)

From LibTx Require Import
     Storage.Classes.

From SLOT Require Import
     Foundations
     Commutativity
     Tactics.

From Hammer Require Import
     Tactics.

Class DeterministicHandler (Req : Type) (Ret : Req -> Type) :=
  { det_h_state : Type;
    det_h_state_transition : forall (pid : PID) (s : det_h_state) (req : Req), det_h_state * Ret req;
  }.

Global Instance deterministicHandler `{d : DeterministicHandler} : @IOHandler Req Ret :=
  { h_state_transition s te s' :=
      match te with
      | proc_te pid (iop req ret) =>
        let (s'_, ret_) := det_h_state_transition pid s req in
        s' = s'_ /\ ret = ret_
      end;
  }.

Global Arguments deterministicHandler {_} {_}.

Module Var.
  Section defs.
    Context {T : Type}.

    Inductive req_t :=
    | read
    | write : T -> req_t.

    Definition ret_t req :=
      match req with
      | read => T
      | write _ => True
      end.

    Definition step (_ : PID) s req : T * ret_t req :=
      match req with
      | read => (s, s)
      | write new => (new, I)
      end.

    Global Instance varDetHandler : DeterministicHandler req_t ret_t :=
      { det_h_state := T;
        det_h_state_transition := step;
      }.
  End defs.

  Definition t T := deterministicHandler (@varDetHandler T).

  Lemma var_rr_comm {T pid1 pid2 r1 r2} :
    events_commute (pid1 @ r1 <~ @read T) (pid2 @ r2 <~ read).
  Proof.
    unfold events_commute. intros s s'.
    sauto.
  Qed.

  Lemma var_ww_comm {T pid1 pid2} {v1 v2 : T} :
    v1 <> v2 ->
    not (events_commute (pid1 @ I <~ write v1) (pid2 @ I <~ write v2)).
  Proof.
    intros Hv H.
    unfold events_commute in H. sauto.
  Qed.
End Var.

Module Log.
  Section defs.
    Context {Event : Type}.

    Definition State : Type := list (PID * Event).

    Inductive req_t := log : Event -> req_t.

    Definition ret_t := I.

    Definition step (pid : PID) (s : State) (req : req_t) :=
      match req with
      | log content =>
          ((pid, content) :: s, ret_t)
      end.

    Instance historyDetHandler : DeterministicHandler req_t (fun _ => True) :=
      { det_h_state := State;
        det_h_state_transition := step;
      }.
  End defs.

  Definition t Event := deterministicHandler (@historyDetHandler Event).
End Log.

Global Arguments Log.t : clear implicits.

Module ProcessDictionary.
  Section defs.
    Context {Val St : Type} `{Storage PID Val St}.

    Inductive req_t : Type :=
    | pd_get
    | pd_erase
    | pd_put : Val -> req_t.

    Definition ret_t req : Type :=
      match req with
      | pd_get => option Val
      | pd_put _ => True
      | pd_erase => True
      end.

    Definition State := St.

    Definition step (pid : PID) (s : State) (req : req_t) : State * ret_t req :=
      match req with
      | pd_get => (s, get pid s)
      | pd_put new_val => (put pid new_val s, I)
      | pd_erase => (delete pid s, I)
      end.

    Global Instance processDictDetHandler : DeterministicHandler req_t ret_t :=
      { det_h_state := State;
        det_h_state_transition := step;
      }.

    Definition t := deterministicHandler processDictDetHandler.
  End defs.

  Global Arguments t {_}.
End ProcessDictionary.

Module Self.
  Inductive req_t := self.

  Global Instance selfDetHandler : DeterministicHandler req_t (fun _ => PID) :=
    { det_h_state := True;
      det_h_state_transition pid _ _ := (I, pid)
    }.

  Definition t := deterministicHandler selfDetHandler.
End Self.

Module KVsnap.
  Section defs.
    Context {K V State} `{Hstate : KeysSnapshot K V State}.

    Inductive req_t :=
    | kv_apply : @Wlog_elem K V -> req_t
    | kv_read : K -> req_t
    | kv_keys : req_t.

    Definition ret_t req : Type :=
      match req with
      | kv_apply _ => True
      | kv_read _ => option V
      | kv_keys => list K
      end.

    Definition step (_ : PID) (s : State) (req : req_t) : State * ret_t req :=
      match req with
      | kv_apply op => (wlog_elem_apply op s, I)
      | kv_read k => (s, get k s)
      | kv_keys => (s, keys_snapshot s)
      end.

    Global Instance varDetHandler : DeterministicHandler req_t ret_t :=
      { det_h_state := State;
        det_h_state_transition := step;
      }.

    Definition t := deterministicHandler varDetHandler.
  End defs.

  Global Arguments t {_} {_} State {_} {_}.
End KVsnap.
