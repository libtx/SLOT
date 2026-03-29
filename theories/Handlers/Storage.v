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
  Context {Key Val Container : Type} `(Hstor : stor.Storage Key Val Container) `{Heqdec : EqDec.EqDec Key eq}.

  Program Definition storage_get (k : Key) : @MFunRet (option Val) Container (eq_setoid _) stor.s_eq_setoid :=
    {| morphism s x :=
         x = (stor.get k s, s)
    |}.
  Next Obligation.
    sauto unfold: exists_equiv,stor.get.
  Qed.

  Program Definition storage_put (k : Key) (v : Val) : MFunRet True Container :=
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

  Program Definition storage_delete (k : Key) : MFunRet True Container :=
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

  Definition storage_mfun (req : StorageReq) : MFunRet (StorageRet req) Container :=
    match req with
    | get k => storage_get k
    | put k v => storage_put k v
    | delete k => storage_delete k
    end.

  Instance storageHandler : @IOHandler StorageReq StorageRet :=
    {|
      h_state := Container;
      h_setoid := stor.s_eq_setoid;
      h_handler _ req := storage_mfun req;
      h_initial := stor.new;
      h_spawn _ _ := id;
      h_spawn_covariance _ _ _ _ H := H;
      h_terminate _ := id_mfun;
    |}.
End storage_handler.

Global Arguments storageHandler (_ _) {_} (_).
