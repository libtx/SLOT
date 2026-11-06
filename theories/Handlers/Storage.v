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

From LibTx Require Storage.
Module stor := LibTx.Storage.Classes.

From Stdlib Require Import
  Classes.EquivDec
  SetoidClass
  SetoidDec.

Require Import
  Setoids
  Multifunction
  IOHandler.

From Hammer Require Import
  Tactics.

Module EqDec := EquivDec.

Section storage_handler.
  Context
    {Key Val Container : Type} `{Heqdec : EqDec.EqDec Key eq}
    `(Hstor : stor.Storage Key Val Container).

  Let container_setoid := @stor.s_eq_setoid Key Val Container Hstor.

  Let mfun_t Ret := @MFunRet Ret Container Container (eq_setoid Ret) container_setoid container_setoid.

  Program Definition storage_get (k : Key) : mfun_t (option Val) :=
    {| morphism s x :=
         x = (stor.get k s, s)
    |}.
  Next Obligation.
    sauto unfold: exists_equiv,stor.get.
  Qed.

  Program Definition storage_put (k : Key) (v : Val) : mfun_t True :=
    {| morphism s x :=
         x = (I, stor.put k v s)
    |}.
  Next Obligation.
    exists (I, stor.put k v x'). split.
    - reflexivity.
    - destruct t. split.
      + reflexivity.
      + now rewrite H.
  Qed.

  Program Definition storage_delete (k : Key) : mfun_t True :=
    {| morphism s x :=
        x = (I, stor.delete k s)
    |}.
  Next Obligation.
    exists (I, stor.delete k x'). split.
    - reflexivity.
    - destruct t. split.
      + reflexivity.
      + now rewrite H.
  Qed.

  Inductive StorageReq : Type :=
  | get : Key -> StorageReq
  | put : Key -> Val -> StorageReq
  | delete : Key -> StorageReq.

  Definition StorageRet (req : StorageReq) : Type :=
    match req with
    | get k => option Val
    | put k v => True
    | delete k => True
    end.

  Definition storage_mfun (req : StorageReq) : mfun_t (StorageRet req) :=
    match req with
    | get k => storage_get k
    | put k v => storage_put k v
    | delete k => storage_delete k
    end.

  Definition storage_h_perform_io (pid : Pid) (req : StorageReq) : mfun_t (StorageRet req) :=
    storage_mfun req.

  Instance storageHandler :
    @IOHandler_basics StorageReq StorageRet :=
    {|
      h_state := Container;
      h_setoid := container_setoid;
      h_perform_io := storage_h_perform_io;
      h_initial := stor.new;
      h_spawn := fun _ _ => id_mfun;
      h_terminate := fun _ _ => id_mfun;
    |}.

  Program Instance storageSpawnSpawn : IOHandler_spawn_spawn.
  Solve All Obligations with sauto.
End storage_handler.

Global Arguments storageHandler {_ _ _} (_) {_ _}.
