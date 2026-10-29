From LibTx Require Storage.
Module stor := LibTx.Storage.Classes.

From Stdlib Require Import
  Classes.EquivDec
  SetoidClass
  SetoidDec.

Require Import
  Setoids
  Multifunction
  IOHandler
  Ref.

From Hammer Require Import
  Tactics.

Module EqDec := EquivDec.

Section storage_handler.
  Context {Key Val Container : Type} `(Hstor : stor.Storage Key Val Container) `{Heqdec : EqDec.EqDec Key eq}.

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

  Definition storage_h_handler (pid : Ref) (rc : Fresh.t)
    (pid_valid : Fresh.is_valid_ref pid rc = true) (req : StorageReq) :
    mfun_t (StorageRet req) :=
    storage_mfun req.

  Instance storageHandler : @IOHandler StorageReq StorageRet :=
    {|
      h_state := Container;
      h_setoid := container_setoid;
      h_handler := storage_h_handler;
      h_initial := stor.new;
      h_spawn := fun _ _ _ _ => id_mfun;
      h_spawn_commutativity := ltac:(sauto);
      h_terminate := fun _ _ _ _ => id_mfun;
      h_handler_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_spawn_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      h_terminate_rc_covariance := ltac:(intros; eapply morphism_covariance; eauto);
      (* h_spawn_terminate_commutativity := ltac:(sauto); *)
    |}.
End storage_handler.

Global Arguments storageHandler (_ _) {_} (_).
