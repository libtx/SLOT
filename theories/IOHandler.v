(* SLOT, a formally verified model checker
   Copyright (C) 2021-2026  k32

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

From Stdlib Require Import
  List
  ZArith
  SetoidClass.

Import ListNotations.

From SLOT Require Import
  Setoids
  TransitionSystem
  Ref
  Queue.

From Hammer Require Import
  Tactics.

Definition Pid : Set := Ref.

Section mailbox.
  Inductive Message {AppMessage} :=
  | appmsg : AppMessage -> Message.

  (** Contents of the mailbox *)
  Record Mailbox := {
      mb_t : Set;
      mb_q : @Queue (@Message mb_t);
    }.

  (** Handler state *)
  Let t := Ref.FMap.M.t Mailbox.

  (** "Address" of the mailbox *)
  Record Address {mba_t : Set} :=
    mkAddress
    {
      mba_pid : Ref
    }.

  Definition node_of {mba_t} (a : @Address mba_t) : option positive :=
    match a with
    | {| mba_pid := [] |} => None
    | {| mba_pid := (a :: l) |} => Some a
    end.
End mailbox.

Section IOHandler.
  Context {Request : Type} {Reply : Request -> Type}.

  Class IOHandler := {
      h_state : Type;
      h_setoid : Setoid h_state;
      h_initial : h_state;

      h_perform_io (pid : Pid) (req : Request) : MFunRet (Reply req) h_state h_state;

      h_spawn (pid : Pid) (mailbox_t : Set) : MFun h_state h_state;

      h_terminate (normal : bool) (pid : Pid) : MFun h_state h_state;
    }.

  (** Subclass of IOHandler where spawn effect handler is commutative *)
  Class IOHandler_spawn_spawn `{IOHandler} := {
      h_spawn_commutativity :
          forall (pid1 pid2 : Pid)
             (mb_t1 mb_t2 : Set),
          pid1 <> pid2 ->
          swappable (h_spawn pid1 mb_t1) (h_spawn pid2 mb_t2);
    }.

  (** Subclass of IOHandler where exit effect handler is commutative *)
  Class IOHandler_exit_exit `{IOHandler} := {
      h_exit_commutativity :
         forall (pid1 pid2 : Pid),
           pid1 <> pid2 ->
           swappable (h_terminate true pid1) (h_terminate true pid2)
    }.

  (** Subclass of IOHandler where terminate and spawn effect handlers semi-commute *)
  Class IOHandler_exit_spawn `{IOHandler} := {
      h_exit_spawn_swap :
        forall child_mb_t {pid1 pid2 : Pid} (new_pid : Pid),
          pid1 <> pid2 ->
          swappable (h_terminate true pid1) (h_spawn new_pid child_mb_t)
    }.

  (** Subclass of IOHandler where exit and I/O effect handlers semi-commute *)
  Class IOHandler_exit_io `{IOHandler} := {
      h_exit_io_swap :
        forall {pid1 pid2 req},
          pid1 <> pid2 ->
          swap_ret (add_ret (h_terminate true pid1)) (h_perform_io pid2 req)
    }.

  (** Subclass of IOHandler where spawn and I/O effect handlers semi-commute *)
  Class IOHandler_spawn_io `{IOHandler} := {
      h_spawn_io_swap :
        forall child_mb_t (req : Request) {new_pid pid : Pid},
          new_pid <> pid ->
          swap_ret (add_ret (h_spawn new_pid child_mb_t)) (h_perform_io pid req)
    }.
End IOHandler.

Definition h_request_t `(IOHandler) : Type := Request.
Definition h_reply_t `(IOHandler) : Request -> Type := Reply.
