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

From SLOT Require Import
  VM.

From Hammer Require Import
  Tactics.

Module EqDec := EquivDec.

Section storage_handler.
  Context
    {Ctx : Type} `{Hctx : VMContext Ctx}
    {Key Val Container : Type}
    `(Hstor : stor.Storage Key Val Container) `{Heqdec : EqDec.EqDec Key eq}.

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

  Definition storage_h_perform_io
    (pid : Pid) (ctx : Ctx) (pid_valid : is_valid_pid pid ctx) (req : StorageReq) :
    mfun_t (StorageRet req) :=
    storage_mfun req.

  Instance storageHandler_basics :
    @IOHandler_basics Ctx _ StorageReq StorageRet :=
    {|
      h_state := Container;
      h_setoid := container_setoid;
      h_perform_io := storage_h_perform_io;
      h_initial := stor.new;
      h_spawn := fun _ _ _ _ => id_mfun;
      h_terminate := fun _ _ _ _ => id_mfun;
      h_perform_io_ctx_covariance := ltac:(intros pid req c c' Hc;
                                     destruct c as [ctx v]; destruct c' as [ctx' v'];
                                     cbn; apply simulated_by_refl);
      h_spawn_ctx_covariance := ltac:(intros pid mb_t c c' Hc;
                                 destruct c as [ctx v]; destruct c' as [ctx' v'];
                                 cbn; apply simulated_by_refl);
      h_terminate_ctx_covariance := ltac:(intros normal pid c c' Hc;
                                   destruct c as [ctx v]; destruct c' as [ctx' v'];
                                   cbn; apply simulated_by_refl);
    |}.

  Instance storageHandler :
    @IOHandler Ctx _ StorageReq StorageRet storageHandler_basics :=
    {|
      h_spawn_commutativity := ltac:(intros pid1 pid2 mb_t1 mb_t2
                                         ctx1 ctx2 ctx1' ctx2' f1 f1' f2 f2' Hne x y;
                                     split; intros [z [H1 H2]];
                                     (exists y; split;
                                      [ exists z; split; assumption
                                      | reflexivity ]));
      h_spawn_terminate_commutativity :=
        ltac:(intros normal pid1 pid2 mb_t ctx1 ctx2 ctx1' ctx2'
                    v1 v1' f2 f2' Hne x y;
              split; intros [z [H1 H2]];
              (exists y; split;
               [ exists z; split; assumption
               | reflexivity ]));
    |}.
End storage_handler.

Global Arguments storageHandler_basics {_ _} (_ _ _).
Global Arguments storageHandler {_ _} {_ _} (_).
