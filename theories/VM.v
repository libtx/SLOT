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
  SetoidClass
  SetoidDec.
Import ListNotations.

From SLOT Require
  Setoids
  TransitionSystem
  Ref
  ListSelector
  IOHandler
  RestrictedPermutation.

From LibTx Require Import
  Storage
  Storage.Properties.

Import Setoids TransitionSystem ListSelector Ref.FMap RestrictedPermutation.
Export Ref IOHandler.

From Hammer Require Import
  Hammer.

From RecordUpdate Require Import
  RecordUpdate.

Open Scope positive_scope.

Opaque put.
Opaque get.

Infix "=h=" := (@equiv _ h_setoid) (at level 50) : slot_scope.

Open Scope slot_scope.

Section definitions.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler_basics Request Reply}.

  Let World := @h_state _ _ IOH.

  Let Hequiv_w := @h_setoid _ _ IOH.

  (** ** Processes
   *** Programs
   [Program] datatype defines all primitives used by the business logic.
   *)
  CoInductive Program (Mailbox : Set) : Type :=
  (** Program termintes: *)
  | exit :
    Program Mailbox
  (** Program is doing I/O: *)
  | p_io :
    forall (pending_req : Request)
      (continuation : Reply pending_req -> Program Mailbox),
      Program Mailbox
  (** Program spawns a child process: *)
  | p_spawn :
    forall {Mailbox' : Set}
      (child : @Program Mailbox')
      (continuation : @Address Mailbox' -> Program Mailbox),
      Program Mailbox
  (** A special instruction that halts the VM *)
  | p_halt :
    forall (node : positive),
      Program Mailbox.

  (** Note on the (missing) yield primitive:

      Yield can be used to softly introduce the concept of Erlang's
      "reductions", and to side-step termination checker, making
      programs non-Turing in a practically useful, as opposed to
      forced, way.

      In Erlang, reduction counting improves responsiveness of the
      system, in SLOT it *additionally* gives a structural argument
      "for free".

      We don't introduce it explicitly to save ourselves time the on
      commutativity lemmas, but it can be emulated by a NOP I/O
      handler. *)

  (** *** Process
      [Process] is defined via its pid,
      type of messages it can receive in the main mailbox ([proc_mb_t]),
      and continuation, which is [Program]. *)
  Record Process :=
    mkProcess
      { pid : Pid;
        proc_mb_t : Set;
        cont : @Program proc_mb_t;
      }.

  (* begin hide *)
  #[export] Instance etaProc : Settable _ := settable! mkProcess <pid; proc_mb_t; cont>.
  (* end hide *)

  (** ** VM
      [VM] record defines state of the entire VM.
   *)
  Record VM :=
    mkVM
      { (** State of the I/O handler: *)
        world : World;
        (** Set of runnable processes: *)
        runq : list Process;
        (** Counter that gets incremented when process creates a reference: *)
        ref_ctr : Ref.Fresh.t;
      }.

  Definition vm_eq (a b : VM) : Prop :=
    world a = world b /\ runq a = runq b /\ ref_ctr a = ref_ctr b.

  (* begin hide *)
  #[export] Instance etaVM : Settable _ := settable! mkVM <world; runq; ref_ctr>.
  (* end hide *)

  Program Instance vm_setoid : Setoid VM :=
    {| equiv (a b : VM) :=
        match a, b with
          {| world := w1; runq := rq1; ref_ctr := rc1 |},
          {| world := w2; runq := rq2; ref_ctr := rc2 |} =>
            w1 =h= w2 /\ rc1 =s= rc2 /\ rq1 =p= rq2
        end
    |}.
  Next Obligation.
    Ltac slv := sauto use:Permutation_sym,Permutation_trans.
    split; unfold Reflexive,Symmetric,Transitive.
    - intros a. destruct a; slv.
    - intros a b. destruct a, b; slv.
    - intros a b c. destruct a, b, c. repeat split; slv.
  Qed.

  (** ** VM transition *)

  Definition prog_result {mb_t} (prog : Program mb_t) : Type :=
    match prog with
    | exit _ => True
    | p_halt _ _ => True
    | p_io _ req _ => Reply req
    | p_spawn _ _ _ => Pid
    end.

  Record TR :=
    { tr_proc : Process;
      tr_result : prog_result (cont tr_proc)
    }.

  (* begin hide *)
  #[export] Instance tr_setoid : Setoid TR := eq_setoid TR.
  (* end hide *)

  (** ** Canonical order *)

  (** Order of events is canonical when pid a >= pid b: *)
  Definition vmte_canon_rel (a b : Process) : bool :=
    match RefOrd.compare_ (pid a) (pid b) with
    | Lt => false
    | _ => true
    end.

  Lemma vmte_canon_rel_total a b :
    vmte_canon_rel a b = true \/ vmte_canon_rel b a = true.
  Proof.
    unfold vmte_canon_rel.
    remember (RefOrd.compare_ (pid a) (pid b)) as ord.
    destruct ord.
    - now left.
    - right. symmetry in Heqord. apply RefOrd.compare_antisymm in Heqord.
      now rewrite Heqord.
    - now left.
  Qed.

  Global Instance vmevCanonOrder : CanonicalOrder vmte_canon_rel :=
    { canon_rel_total := vmte_canon_rel_total;
    }.

  Definition MaybeValidProc : Type := option (Process * VM).

  Program Definition schedule_out : @MFun VM MaybeValidProc vm_setoid (setoid_option _) :=
      {| morphism vm ret :=
          match vm with
            {| world := w; runq := rq; ref_ctr := rc |} =>
              match rq with
              | [] =>
                  ret = None
              | _ =>
                  match ret with
                  | None => False
                  | Some (proc, {| world := w'; runq := rq'; ref_ctr := rc' |}) =>
                      rq ~[pick_mfun]~> (proc, rq') /\
                        w = w' /\
                        rc = rc'
                  end
              end
          end
      |}.
  Next Obligation.
    destruct x as [w rq rc].
    destruct x' as [w' rq' rc'].
    destruct rq as [|rq_ rq_rest]; simpl in *;
      destruct H as [Hw [Hrc Hperm]].
    - exists None. split.
      + destruct rq' as [|rq'_ rq'_rest]; try easy.
        now apply Permutation_nil in Hperm.
      + now subst.
    - destruct y as [[proc vm2]|]; try easy.
      destruct vm2 as [w2 rq2 rc2].
      destruct H0 as [Hpick_proc [Hw2 Hrc2]].
      subst.
      apply pick_equiv with (l1' := rq') in Hpick_proc; try easy.
      destruct Hpick_proc as [rq2' [Hpick_proc' Hrq2']].
      exists (Some (proc, {|world := w'; runq := rq2'; ref_ctr := rc' |})).
      simpl. split; [|split]; try easy.
      destruct rq' as [|rq'_ rq'_rest].
      + exfalso.
        now apply Permutation_sym, Permutation_nil in Hperm.
      + now repeat split.
  Qed.

  Lemma schedule_out_some vm0 vm1 proc :
    Some (proc, vm1) <~[schedule_out]~ vm0 ->
    (runq vm0) ~[pick_mfun]~> (proc, runq vm1) /\
      (world vm0) = (world vm1) /\
      (ref_ctr vm0) = (ref_ctr vm1).
  Proof.
    intros H.
    destruct vm0 as [w0 rq0 rc0].
    destruct vm1 as [w1 rq1 rc1].
    simpl in H.
    destruct rq0 as [|f r].
    - exfalso. discriminate.
    - assumption.
  Qed.

  (** ** Operations with the world *)

  Program Definition lift_w (w_morph : @MFun World World Hequiv_w Hequiv_w) : @MFun VM VM vm_setoid vm_setoid :=
    {| morphism vm1 vm2 :=
        match vm1, vm2 with
          {| world := w1; runq := rq1; ref_ctr := rc1 |},
          {| world := w2; runq := rq2; ref_ctr := rc2 |} =>
            w1 ~[w_morph]~> w2 /\
            rq1 = rq2 /\
            rc1 = rc2
        end;
    |}.
  Next Obligation.
    destruct x as [w1 rq1 rc1].
    destruct x' as [w1' rq1' rc1'].
    destruct y as [w2 rq2 rc2].
    destruct H as [Hw [Hrc Hrq]].
    destruct H0 as [Hw12 [Hrc12 Hrq12]].
    subst.
    apply morphism_covariance with (x' := w1') in Hw12; [|now rewrite Hw].
    destruct Hw12 as [w2' [Hw12' H2]].
    exists {| world := w2'; runq := rq1'; ref_ctr := rc1' |}.
    repeat split; try assumption.
    - apply Hrc.
  Qed.

  Lemma lift_w_commute f g :
    commute f g ->
    commute (lift_w f) (lift_w g).
  Proof.
    intros Hcommute.
    intros [w1 rq1 rc1] [w3 rq3 rc3];
      split;
      intros [[w2 rq2 rc2] [Hvm2 Hvm3]];
      simpl in Hvm2; simpl in Hvm3;
      destruct Hvm2 as [Hw2 [? ?]];
      destruct Hvm3 as [Hw3 [? ?]];
      subst;
      [ assert (H13 : w3 <~[ g ∘ f ]~ w1) by sauto
      | assert (H13 : w3 <~[ f ∘ g ]~ w1) by sauto
      ];
      destruct (Hcommute w1 w3) as [Hfg Hgf];
      [ destruct (Hfg H13) as [w3' [Hw3' Hequiv]]
      | destruct (Hgf H13) as [w3' [Hw3' Heqiuv]]
      ];
      destruct Hw3' as [w2' ?];
      exists {| world := w3'; ref_ctr := rc3; runq := rq3 |}.
    - split; [exists {| world := w2'; ref_ctr := rc3; runq := rq3 |} |]; sauto.
    - split; [exists {| world := w2'; ref_ctr := rc3; runq := rq3 |} |]; sauto.
  Qed.

  (** ** Spawn *)

  Section spawn.
    Context
      (parent : Process) (child_mb_t : Set) (child_cont : Program child_mb_t)
      (parent_cont : @Address child_mb_t -> Program (proc_mb_t parent)).

    (** Allocate a new pid for a process and add it to the VM.
        Update the parent process (which should be scheduled out),
        and add it to the VM too. Does not change the world. *)
    Definition alloc_pid (vm : VM) : Pid * VM.
    Proof.
      destruct vm as [w rq rc].
      destruct (Fresh.make (pid parent) rc) as [new rc'].
      set (addr := mkAddress child_mb_t new).
      set (rq' :=
             {| pid := pid parent; proc_mb_t := proc_mb_t parent; cont := parent_cont addr |} ::
             {| pid := new; proc_mb_t := child_mb_t; cont := child_cont |} ::
             rq).
      exact (new, {| world := w; runq := rq'; ref_ctr := rc' |}).
    Defined.

    Lemma alloc_pid_covariance
      (vm vm' : VM)
      (Hvm' : vm == vm') :
      @equiv _ (pair_setoid' (eq_setoid _) vm_setoid) (alloc_pid vm) (alloc_pid vm').
    Proof.
      destruct vm as [w1 rq1 rc1].
      destruct vm' as [w1' rq1' rc1'].
      unfold alloc_pid.
      simpl in Hvm'. destruct Hvm' as [Hw [Hrc Hrq]].
      (* Ref counters: *)
      apply Fresh.make_morph with (parent := pid parent) in Hrc.
      destruct (Fresh.make (pid parent) rc1) as [new_pid rc2].
      destruct (Fresh.make (pid parent) rc1') as [new_pid' rc2'].
      destruct Hrc as [Hnew_pids Hrc2]. simpl in Hnew_pids.
      subst.
      (* Rest *)
      simpl.
      split.
      - easy.
      - split; [|split].
        + assumption.
        + assumption.
        + now repeat apply perm_skip.
    Qed.

    (** TR of the spawn step: the scheduled out parent process with
        the pid allocated for the child as the result. *)
    Definition spawn_tr (new_pid : Pid) : TR :=
      {| tr_proc :=
           {| pid := pid parent; proc_mb_t := proc_mb_t parent;
              cont := p_spawn (proc_mb_t parent) child_cont parent_cont |};
         tr_result := new_pid
      |}.

    (** Allocate a new pid for a process and add it to the VM.
        Update the parent process (which should be scheduled out),
        and add it to the VM too. *)
    Definition spawn_morph (vm0 : VM) (ret : TR * VM) : Prop :=
      let (new_pid, vm1) := alloc_pid vm0 in
      let (tr, vm2) := ret in
      exists2 w2 : World,
          (world vm1) ~[h_spawn new_pid child_mb_t]~> w2 &
          tr = spawn_tr new_pid /\
          vm2 = vm1<|world := w2|>.

    Lemma spawn_morph_covariance :
      forall (vm0 vm0' : VM) (ret : TR * VM),
        vm0 == vm0' ->
        spawn_morph vm0 ret ->
        exists{ret' == ret}, spawn_morph vm0' ret'.
    Proof.
      intros vm0 vm0' [tr vm2] Hvm0 Hvm.
      unfold spawn_morph in *.
      specialize (alloc_pid_covariance vm0 vm0' Hvm0) as Hvm1'.
      destruct (alloc_pid vm0) as [new_pid vm1].
      destruct (alloc_pid vm0') as [new_pid' vm1'].
      destruct Hvm1' as [Hnew_pid Hvm1']. simpl in Hnew_pid.
      destruct Hvm as [w2 Hw2 [Htr Hvm2]].
      subst.
      destruct vm1 as [w1 rq1 rc1].
      destruct vm1' as [w1' rq1' rc1'].
      destruct Hvm1' as [Hw1 [Hrc1 Hrq1]].
      morph_shift (h_spawn new_pid' child_mb_t) w1'.
      exists (spawn_tr new_pid', {| world := w2'; runq := rq1'; ref_ctr := rc1' |}).
      split.
      - now exists w2'.
      - easy.
    Qed.

    Definition spawn : MFunRet TR VM VM :=
      {| morphism := spawn_morph;
         morphism_covariance := spawn_morph_covariance;
      |}.
  End spawn.

  Section io.
    Context
      (proc : Process) (req : Request)
      (cnt : Reply req -> Program (proc_mb_t proc)).

    Let ret_t := Reply req.

    (** TR of the I/O step: the scheduled out process with the I/O
        reply as the result. *)
    Definition perform_io_tr (rep : ret_t) : TR :=
      {| tr_proc :=
           {| pid := pid proc; proc_mb_t := proc_mb_t proc;
              cont := p_io (proc_mb_t proc) req cnt |};
         tr_result := rep
      |}.

    Definition perform_io_morph (vm1 : VM) (ret : TR * VM)  : Prop :=
      let (w1, rq1, rc1) := vm1 in
      let (tr, vm2) := ret in
      let (w2, rq2, rc2) := vm2 in
      exists rep : ret_t,
        w1 ~[h_perform_io (pid proc) req]~> (rep, w2) /\
        tr = perform_io_tr rep /\
        rc2 = rc1 /\
        rq2 = {| pid := pid proc; proc_mb_t := proc_mb_t proc; cont := cnt rep |} :: rq1.

    Lemma perform_io_morph_covariance :
      forall (vm1 vm1' : VM) (ret : TR * VM),
        vm1 == vm1' ->
        perform_io_morph vm1 ret ->
        exists{ret' == ret}, perform_io_morph vm1' ret'.
    Proof.
      intros x x' [tr vm2] H H0.
      destruct x as [w1 rq1 rc1].
      destruct x' as [w1' rq1' rc1'].
      destruct vm2 as [w2 rq2 rc2].
      destruct H as [Hw_eq [Hrc_eq Hrq_eq]].
      destruct H0 as [rep [Hw [Htr [Hrc Hrq]]]].
      subst.
      apply morphism_covariance with (x' := w1') in Hw; [|assumption].
      destruct Hw as [[ret2' w2'] [Hw2' [Hret2_eq' Hw2_eq']]].
      simpl in Hret2_eq'. subst ret2'.
      exists (perform_io_tr rep, {| world := w2';
               runq := {| pid := pid proc; proc_mb_t := proc_mb_t proc; cont := cnt rep |} :: rq1';
               ref_ctr := rc1';
            |}).
      repeat split; try easy.
      - now exists rep.
      - apply Hrc_eq.
      - now constructor.
    Qed.

    Definition perform_io : MFunRet TR VM VM :=
      {| morphism := perform_io_morph;
         morphism_covariance := perform_io_morph_covariance;
      |}.
  End io.

  Section exit.
    Context (proc : Process).

    (** TR of the terminate step: the scheduled out process with the
        trivial result. *)
    Definition terminate_tr : TR :=
      {| tr_proc :=
           {| pid := pid proc; proc_mb_t := proc_mb_t proc;
              cont := exit (proc_mb_t proc) |};
         tr_result := I
      |}.

    Definition terminate_morph (vm1 : VM) (ret : TR * VM) : Prop :=
      let (tr, vm2) := ret in
      vm1 ~[lift_w (h_terminate true (pid proc))]~> vm2 /\
        tr = terminate_tr.

    Lemma terminate_morph_covariance :
      forall (vm1 vm1' : VM) (ret : TR * VM),
        vm1 == vm1' ->
        terminate_morph vm1 ret ->
        exists{ret' == ret}, terminate_morph vm1' ret'.
    Proof.
      intros x x' [tr vm2] H H0.
      destruct x as [w1 rq1 rc1].
      destruct x' as [w1' rq1' rc1'].
      destruct vm2 as [w2 rq2 rc2].
      cbn in H. destruct H as [Hw1 [Hrc1 Hrq1]].
      cbn in H0. destruct H0 as [[Hterm [Hrq13 Hrc13]] Htr].
      morph_shift (h_terminate true (pid proc)) w1'.
      subst.
      exists (terminate_tr, {| world := w2'; runq := rq1'; ref_ctr := rc1' |}).
      split.
      - cbn. repeat split; try easy.
      - easy.
    Qed.

    Definition terminate : MFunRet TR VM VM :=
      {| morphism := terminate_morph;
         morphism_covariance := terminate_morph_covariance;
      |}.
  End exit.

  Definition exec_proc_morph (proc : Process) (vm1 vm2 : VM) : Prop :=
    match cont proc with
    | exit _ =>
        exists tr, vm1 ~[terminate proc]~> (tr, vm2)
    | p_io _ req cont =>
        exists tr, vm1 ~[perform_io proc req cont]~> (tr, vm2)
    | @p_spawn _ child_mb_t child_cont parent_cont =>
        exists tr, vm1 ~[spawn proc child_mb_t child_cont parent_cont]~> (tr, vm2)
    | _ =>
        False
    end.

  Lemma exec_proc_morph_covariance (proc : Process) vm0 vm0' vm1 :
    vm0 == vm0' ->
    exec_proc_morph proc vm0 vm1 ->
    exists{vm1' == vm1}, exec_proc_morph proc vm0' vm1'.
  Proof.
    intros Hvm0 Hvm2.
    destruct proc as [pid mb_t prog].
    destruct prog; cbn [cont exec_proc_morph] in *;
      try easy; unfold exists_equiv;
      lazymatch goal with
      | [ Hx : exists _, _ ~[ ?f ]~> (_, _) |- _ ] =>
          destruct Hx as [tr Hx];
          apply morphism_covariance with (x' := vm0') in Hx;
          try assumption;
          destruct Hvm2 as [[tr2 vm1'] [Hx Heq]];
          exists vm1'; split;
          [ now exists tr2
          | destruct Heq as [_ Heq2]; assumption ]
      end.
  Qed.

  Definition exec_proc (proc : Process) : MFun VM VM :=
    {| morphism := exec_proc_morph proc;
       morphism_covariance := exec_proc_morph_covariance proc;
    |}.

  Inductive vm_step_morph : VM -> option (Process * VM) -> Prop :=
  | vm_step_nil : forall vm,
      vm ~[schedule_out]~> None ->
      vm_step_morph vm None
  | vm_step_some : forall vm0 vm1 vm2 proc,
      vm0 ~[schedule_out]~> Some (proc, vm1) ->
      exec_proc_morph proc vm1 vm2 ->
      vm_step_morph vm0 (Some (proc, vm2)).

  Lemma vm_step_morph_covariance vm0 vm0' vm2 :
    vm0 == vm0' ->
    vm_step_morph vm0 vm2 ->
    exists{vm2' == vm2}, vm_step_morph vm0' vm2'.
  Proof.
    intros Hequiv H0.
    inversion H0 as [|H vm1 ? proc Hvm1 Hvm2]; subst; clear H0.
    - exists None.
      split; [|easy].
      constructor.
      apply morphism_covariance with (x' := vm0') in H; [|easy].
      destruct H as [x [H1 H2]].
      now destruct x.
    - apply morphism_covariance with (x' := vm0') in Hvm1;[|easy].
      destruct Hvm1 as [vm1' [Hvm1' Hvm1'equiv]].
      destruct vm1'; [|easy].
      destruct p as [proc' vm1'].
      destruct Hvm1'equiv as [Hproc Hvm1'equiv].
      simpl in Hproc.
      subst.
      apply exec_proc_morph_covariance with (vm0' := vm1') in Hvm2; [|easy].
      destruct Hvm2 as [vm2' [Hvm2' Hvm2'equiv]].
      exists (Some (proc', vm2')).
      split.
      + now constructor 2 with (vm1 := vm1').
      + easy.
  Qed.

  Definition vm_step : @MFun VM (@ts_ret VM Process) vm_setoid (ts_ret_setoid Process vm_setoid) :=
    {| morphism := vm_step_morph;
       morphism_covariance := vm_step_morph_covariance;
    |}.

  Global Instance vmTransitionSystem : @TransitionSystem VM Process :=
    {|
      ts_setoid := vm_setoid;
      ts_canon_rel := vmte_canon_rel;
      ts_canon_order := vmevCanonOrder;
      ts_state_trans := vm_step
    |}.
End definitions.

From Ltac2 Require
  Fresh
  String
  Ident
  Std
  Ident
  Constr
  Control.
From Ltac2 Require Import
  Notations
  Printf
  Init.
From SLOT Require Import
  Tactics.

Set Default Proof Mode "Ltac2".

Ltac2 dvm (vms : ident list) :=
  List.iter
    (fun vm =>
       let prefix := Ident.to_string vm in
       let w := fresh_id (String.app prefix "_w") in
       let rq := fresh_id (String.app prefix "_rq") in
       let rc := fresh_id (String.app prefix "_rc") in
       let vm_ := Control.hyp vm in
       match! Constr.type vm_ with
       | VM =>
           destruct $vm_ as [$w $rq $rc]
       end)
    vms.

Ltac2 Notation "dvm" ids(list0(ident)) := dvm ids.

(* begin hide *)
Section tests.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler_basics Request Reply}.

  (* test [dvm] tactic *)
  Goal forall (vm1 vm2 : VM), vm1 = vm2 -> False.
    intros vm1 vm2 H.
    dvm vm1 vm2.
  Abort.
End tests.
(* end hide *)

Section canned.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler_basics Request Reply}.

  Lemma canned_schedule_out_some proc vm0 vm1 :
    Some (proc, vm1) <~[schedule_out]~ vm0 ->
    Pick (runq vm0) proc (runq vm1) /\
      world vm0 = world vm1 /\
      ref_ctr vm0 = ref_ctr vm1.
  Proof.
    intros H.
    dvm vm0 vm1.
    simpl in *.
    destruct vm0_rq as [|a b].
    - discriminate.
    - assumption.
  Qed.

  Lemma Permutation_swap2 {A} (a1 b1 a2 b2 : A) l1 l2 :
    l1 =p= l2 ->
    (a1 :: b1 :: a2 :: b2 :: l1) =p= (a2 :: b2 :: a1 :: b1 :: l2).
  Proof.
    intros Hl.
    change (a1 :: b1 :: a2 :: b2 :: l1) with ([a1; b1] ++ [a2; b2] ++ l1).
    change (a2 :: b2 :: a1 :: b1 :: l2) with ([a2; b2] ++ [a1; b1] ++ l2).
    eapply Permutation_trans with (l' := [a1; b1] ++ [a2; b2] ++ l2).
    - apply Permutation_app_head.
      apply Permutation_app_head.
      exact Hl.
    - rewrite !app_assoc.
      apply Permutation_app_tail.
      apply Permutation_app_comm.
  Qed.
End canned.

Ltac2 maybe_hyp_to_string (c : constr) (default : string) : string :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var c => Ident.to_string c
  | _ => default
  end.

(* Destruct the [exec_proc_morph] conclusion that the hypothesis
   [id] (already unfolded down to the level of perform_io / lift_w /
   do_spawn / spawn) is left with. *)
Ltac2 rec unfold_exec_proc_morph (id : ident) :=
  let hyp_prefix := Ident.to_string id in
  let hworld := fresh_id (String.app hyp_prefix "_w") in
  let hrq := fresh_id (String.app hyp_prefix "_rq") in
  let hrc := fresh_id (String.app hyp_prefix "_rc") in
  let new_hyp := Control.hyp id in
  lazy_match! Constr.type new_hyp with
  | context [@ex _ (fun tr => @morphism _ _ _ _ _ _ (tr, _))] =>
      let tr := fresh_id "tr" in
      destruct $new_hyp as [$tr $id];
      unfold_exec_proc_morph id
  | context [@ex _ (fun tr => terminate_morph _ _ (tr, _))] =>
      let tr := fresh_id "tr" in
      destruct $new_hyp as [$tr $id];
      unfold_exec_proc_morph id
  | context [@ex _ (fun tr => spawn_morph _ _ _ _ _ (tr, _))] =>
      let tr := fresh_id "tr" in
      destruct $new_hyp as [$tr $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (terminate _) _ _ =>
      unfold terminate in $id;
      destruct $new_hyp as [_vt_exit $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (perform_io _ _ _) _ _ =>
      unfold perform_io in $id;
      destruct $new_hyp as [_vt_io $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (spawn _ _ _ _) _ _ =>
      unfold spawn_morph in $id;
      destruct $new_hyp as [_vt_spawn $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (terminate _) _ _ =>
      unfold terminate in $id;
      cbn in $id;
      unfold_exec_proc_morph id
  | context [@ex _ (fun tr => perform_io_morph _ ?req _ _ (tr, _))] =>
      let rep := fresh_id (String.app (maybe_hyp_to_string req "") "_rep") in
      let htr := fresh_id (String.app hyp_prefix "_tr") in
      let tr := fresh_id "tr" in
      destruct $new_hyp as [$tr [$rep [$hworld [$htr [$hrc $hrq]]]]]
  | perform_io_morph _ ?req _ _ (_, _) =>
      let rep := fresh_id (String.app (maybe_hyp_to_string req "") "_rep") in
      let htr := fresh_id (String.app hyp_prefix "_tr") in
      destruct $new_hyp as [$rep [$hworld [$htr [$hrc $hrq]]]]
  | terminate_morph _ _ (_, _) =>
      unfold terminate_morph in $id;
      cbn in $id;
      unfold_exec_proc_morph id
  | context [@ex _ (fun tr => _ /\ (_ = terminate_tr _))] =>
      let trw := fresh_id (String.app hyp_prefix "_tr") in
      destruct $new_hyp as [$trw $id];
      unfold_exec_proc_morph id
  | _ /\ _ /\ _ =>
      destruct $new_hyp as [$hworld [$hrq $hrc]]
  | _ /\ (_ = _) =>
      destruct $new_hyp as [$id _];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (spawn _ _ _ _) _ _ =>
      (* The spawn step of [exec_proc_morph] is stated via the [spawn]
         MFun on the sigma type of VMs with a valid parent pid; unfold
         it back into [do_spawn] and retry. *)
      unfold spawn in $id;
      cbn in $id;
      unfold_exec_proc_morph id
  | spawn_morph _ _ _ _ _ (_, _) =>
      let new_pid := fresh_id "new_pid" in
      let new_rc := fresh_id "new_pid_rc" in
      let w2 := fresh_id (String.app hyp_prefix "_spawn_w") in
      let heq_vm := fresh_id (String.app hyp_prefix "_eq_vm") in
      let fresh_make_result := fresh_id (String.app hyp_prefix "_fresh") in
      unfold spawn_morph in $id;
      cbn in $id;
      lazy_match! Constr.type (Control.hyp id) with
      | context [Fresh.make ?parent_mw ?rc_mw] =>
          remember (Fresh.make $parent_mw $rc_mw) as $fresh_make_result;
          let fresh_make_result := Control.hyp fresh_make_result in
          destruct $fresh_make_result as [$new_pid $new_rc]
      end;
      let htr := fresh_id (String.app hyp_prefix "_tr_eq") in
      let new_hyp := Control.hyp id in
      destruct $new_hyp as [$w2 $hworld [$htr $heq_vm]];
      clear $htr;
      (* Unfold equality over the VM *)
      let heq_vm_w := fresh_id "_w" in
      let heq_vm_rq := fresh_id "_rq" in
      let heq_vm_rc := fresh_id "_rc" in
      let heq_vm' := Control.hyp heq_vm in
      injection $heq_vm' as $heq_vm_w $heq_vm_rq $heq_vm_rc; clear $heq_vm;
      let heq_vm_w' := Control.hyp heq_vm_w in
      let heq_vm_rq' := Control.hyp heq_vm_rq in
      let heq_vm_rc' := Control.hyp heq_vm_rc in
      rewrite $heq_vm_w' in *; clear $heq_vm_w;
      rewrite $heq_vm_rq' in *; clear $heq_vm_rq;
      rewrite $heq_vm_rc' in *; clear $heq_vm_rc
  | ?other =>
      printf "No match: %t" other
  end.

Ltac2 unfold_schedule_out (id : ident) :=
  match! Constr.type (Control.hyp id) with
  | ?_vm0 ~[schedule_out]~> Some (?proc, ?vm) =>
      let proc_prefix := maybe_hyp_to_string proc (Ident.to_string id) in
      let world_prefix := maybe_hyp_to_string vm (Ident.to_string id) in
      let hpick := fresh_id (String.app proc_prefix "_pick") in
      let hworld := fresh_id (String.app world_prefix "_w") in
      let hrc := fresh_id (String.app world_prefix "_rc") in
      let tmp := fresh_id "H" in
      apply canned_schedule_out_some in $id as $tmp;
      let tmp := Control.hyp tmp in
      destruct $tmp as [$hpick [$hworld $hrc]];
      cbn in $hworld; cbn in $hrc; cbn in $hpick;
      let hw := Control.hyp hworld in
      let hr := Control.hyp hrc in
      rewrite $hw in *; clear $hworld;
      rewrite $hr in *; clear $hrc;
      clear $id
  end.

Ltac2 Notation "unfold_schedule_out" x(ident) := unfold_schedule_out x.

Ltac2 rec unfold_vm_step_morph (id : ident) :=
  lazy_match! Constr.type (Control.hyp id) with
  | ?_vm0 ~[ ts_mfun ?_step ]~> ?_vm1 =>
      unfold ts_mfun,morphism,ts_state_trans in Hvm2;
      cbn in $id;
      unfold_vm_step_morph id
  | vm_step_morph ?vm_start (Some (?_proc, ?vm_end)) =>
      let prefix := maybe_hyp_to_string vm_start (Ident.to_string id) in
      let vm1 := fresh_id "vm1_" in
      let vm1_out := fresh_id (String.app prefix "_out") in
      let vm3 := fresh_id "vm3_" in
      let proc := fresh_id "proc_" in
      let schedule_out := fresh_id (String.app (String.app "H" prefix) "_out") in
      let h_vm2 := fresh_id "vm2_" in
      let h_vm1 := fresh_id "Hvm1_" in
      let h_proc := fresh_id "Hproc_" in

      iinversion $id as [|$vm1 $vm1_out $vm3 $proc $schedule_out $h_vm2 $h_vm1 $h_proc];
      clear $id; Std.rename [(h_vm2, id)];
      subst $vm1; subst $vm3; subst $proc;
      unfold exec_proc_morph, vm_eq in $id; cbn in $id;
      (* simplify the remaining goals *)
      match Constr.Unsafe.kind vm_start with
      | Constr.Unsafe.Var id => dvm $id
      | _ => ()
      end;
      match Constr.Unsafe.kind vm_end with
      | Constr.Unsafe.Var id => dvm $id
      | _ => ()
      end;
      dvm $vm1_out;
      unfold_schedule_out $schedule_out;
      unfold_exec_proc_morph id
  end.

Ltac2 Notation "unfold_vm_step_morph" x(ident) := unfold_vm_step_morph x.

(* Use equations instead? *)
Ltac2 unfold_alloc_pid (pid : constr) (rc : constr) new_ident :=
  let prefix := Ident.to_string new_ident in
  let new_pid := fresh_id prefix in
  let new_rc := fresh_id (String.app prefix "_rc") in
  destruct (Fresh.make $pid $rc) as [$new_pid $new_rc].

Ltac2 Notation "unfold_alloc_pid" pid(constr) rc(constr) new(seq("as", ident)) := unfold_alloc_pid pid rc new.

Notation "'P<' T > A @ C " := {| pid := A; proc_mb_t := T; cont := C |} (at level 100).

Section commute.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler_basics Request Reply}.

  Let req_t := h_request_t IOH.
  Let rep_t := h_reply_t IOH.
  Let prog_t := @Program req_t rep_t.

  Ltac2 vm_step_some (vm_out : constr) :=
    match! goal with
    | [ |- vm_step_morph ?vm0 (Some (?proc, ?vm2)) ] =>
        let suffix := maybe_hyp_to_string proc "proc" in
        let hproc := fresh_id (String.app "Hinv_" suffix) in
        assert ($hproc : $vm0 ~[schedule_out]~> Some ($proc, $vm_out)) >
          [ |
            let hproc := Control.hyp hproc in
            refine '(vm_step_some $vm0 $vm_out $vm2 $proc $hproc _)
          ]
    end.

  Ltac2 Notation "vm_step_some" vm(constr) := vm_step_some vm.

  Ltac2 swap_make () :=
    lazy_match! goal with
    | [ hpids : ?pid1 <> ?pid2, h1 : Fresh.make ?pid1 _ = (?new1, _), h2 : Fresh.make ?pid2 _ = (?new2, _) |- _ ] =>
        let hpids := Control.hyp hpids in
        let h1 := Control.hyp h1 in
        let h2 := Control.hyp h2 in
        destruct (Fresh.swap_make $pid1 $pid2 $new1 $new2 _ _ _ $hpids $h1 $h2) as [rc2' [rc3' [Hrc' [Hnew_pid1' Hnew_pid2']]]]
    end.

  (* 1/10 *)
  Lemma spawn_spawn_swap `{!IOHandler_spawn_spawn}
    {pid1 pid2 mb_t1 mb_t2 child_mb_t1 child_mb_t2 child1 child2 cont1 cont2} :
    RefOrd.gt pid1 pid2 ->
    tev_semicommute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @p_spawn req_t rep_t mb_t1 child_mb_t1 child1 cont1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_spawn req_t rep_t mb_t2 child_mb_t2 child2 cont2 |}.
  Proof.
    intros Hpids12.
    (* Unfold the original path: *)
    unfold tev_semicommute, semicommute, exists_equiv.
    intros vm0 vm4 [vm2 [Hvm2 Hvm4]].
    unfold_vm_step_morph Hvm2.
    unfold_vm_step_morph Hvm4.
    (* Relations between pids: *)
    assert (Hpids12_ne : pid1 <> pid2). {
      intros Heq.
      apply RefOrd.ref_compare_eq_iff in Heq.
      unfold RefOrd.gt in Hpids12. now rewrite Heq in Hpids12.
    }
    assert (Hpid1_new : RefOrd.compare_ pid1 new_pid = Lt).
    { now apply Fresh.child_gt_parent in HeqHvm2_fresh.
    }
    assert (Hpid2_new : RefOrd.compare_ pid2 new_pid = Lt).
    { apply RefOrd.compare_antisymm in Hpids12.
      now specialize (RefOrd.lt_trans Hpids12 Hpid1_new).
    }
    assert (Hnew_pid2_neq : new_pid <> pid2).
    { intros Habsurd. apply RefOrd.ref_compare_eq_iff,RefOrd.compare_eq_symm in Habsurd.
      now rewrite Hpid2_new in Habsurd.
    }
    assert (Hnew_pids : new_pid <> new_pid0).
    { apply (Fresh.different_parents_children pid1 pid2 new_pid new_pid0 Hpids12_ne HeqHvm2_fresh HeqHvm4_fresh).
    }
    (* Build the run queue *)
    assert (Hne_parent1 : {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 {| mba_pid := new_pid |} |}
                        <> {| pid := pid2; proc_mb_t := mb_t2; cont := p_spawn mb_t2 child2 cont2 |}).
    { (* The second scheduled out process cannot be among the processes
         added to the queue by the first spawn (their pids differ): *)
      intros Heq. injection Heq as Hpid_eq Hmb Hcnt.
      now apply Hpids12_ne in Hpid_eq.
    }
    destruct (pick_cons HHvm4_out_pick Hne_parent1) as [rq_a [Heq_a Hpick_a]].
    subst Hvm4_out_rq.
    assert (Hne_child1 : {| pid := new_pid; proc_mb_t := child_mb_t1; cont := child1 |}
                       <> {| pid := pid2; proc_mb_t := mb_t2; cont := p_spawn mb_t2 child2 cont2 |}).
    { intros Heq. injection Heq as Hpid_eq Hmb Hcnt. now apply Hnew_pid2_neq. }
    destruct (pick_cons Hpick_a Hne_child1) as [rq_b [Heq_b Hpick_b]].
    subst rq_a.
    destruct (pick_two Hvm0_out_pick Hpick_b) as [rq2' [rq3' [Hpick_proc2 [Hpick_proc1 Hrq3'b]]]].
    (* Build the new ref counter *)
    symmetry in HeqHvm2_fresh. symmetry in HeqHvm4_fresh.
    swap_make ().
    (* Build the new world *)
    simpl in Hvm2_w. simpl in Hvm4_w.
    destruct (h_spawn_commutativity new_pid new_pid0 child_mb_t1 child_mb_t2 Hnew_pids vm0_out_w Hvm4_spawn_w) as [w2' [Hw2' Hw2'_equiv]].
    { now exists Hvm4_out_w. }
    exists {| world := w2';
        runq := {| proc_mb_t := mb_t1; pid := pid1; cont := cont1 {| mba_pid := new_pid |} |}
              :: {| proc_mb_t := child_mb_t1; pid := new_pid; cont := child1 |}
              :: ({| proc_mb_t := mb_t2; pid := pid2; cont := cont2 {| mba_pid := new_pid0 |} |}
              :: {| proc_mb_t :=  child_mb_t2; pid := new_pid0; cont := child2 |}
              :: rq3');
        ref_ctr := rc3'
      |}.
    split.
    2:{ split > [|split].
        - assumption.
        - now symmetry.
        - rewrite Hrq3'b.
          now apply Permutation_swap2.
    }
    { destruct Hw2' as [w1' [Hw1' Hw2']].
      exists {| world := w1';
           runq := {| proc_mb_t := mb_t2; pid := pid2; cont := cont2 {| mba_pid := new_pid0 |} |}
                 :: {| proc_mb_t := child_mb_t2; pid := new_pid0; cont := child2 |}
                 :: rq2';
           ref_ctr := rc2'
         |}.
      split.
      - constructor 2 with (vm1 := {| world := vm0_out_w; runq := rq2'; ref_ctr := vm0_out_rc |}).
        + sauto.
        + unfold exec_proc_morph. cbn. unfold spawn_morph,alloc_pid. cbn.
          rewrite Hnew_pid1'. eexists. now exists w1'.
      - simpl.
        constructor 2 with (vm1 := {| world := w1';
                                     runq := {| proc_mb_t := mb_t2; pid := pid2; cont := cont2 {| mba_pid := new_pid0 |} |}
                                           :: {| proc_mb_t := child_mb_t2; pid := new_pid0; cont := child2 |}
                                           :: rq3';
                                     ref_ctr := rc2'
                                   |}).
        + sauto.
        + unfold exec_proc_morph. cbn. unfold spawn_morph,alloc_pid. cbn.
          rewrite Hnew_pid2'. eexists. now exists w2'.
    }
  Qed.

  (* 2/10 *)
  Lemma exit_exit_swap `{!IOHandler_exit_exit} {pid1 pid2 mb_t1 mb_t2} :
    RefOrd.gt pid1 pid2 ->
    tev_semicommute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @exit req_t rep_t mb_t1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @exit req_t rep_t mb_t2 |}.
  Proof.
    intros Hpids vm0 vm2 [vm1 [Hvm1 Hvm2]].
    simpl in Hvm1. simpl in Hvm2.
    unfold_vm_step_morph Hvm1.
    unfold_vm_step_morph Hvm2.
    subst.
    (* Run queue: *)
    destruct (pick_two Hvm0_out_pick HHvm2_out_pick) as [rq2' [rq3' [Hpick_proc2 [Hpick_proc1 Hrq3'b]]]].
    (* World: *)
    specialize (RefOrd.gt_not_eq pid1 pid2 Hpids) as Hpids12_ne.
    destruct (h_exit_commutativity pid1 pid2 Hpids12_ne vm0_out_w vm2_w) as [w2' [[w1' [Hw1' Hw2']] Hw2'_equiv]]. { now exists Hvm2_out_w. }
    (* Build it *)
    exists {| world := w2'; runq := rq3'; ref_ctr := vm2_rc |}.
    split.
    2:{ repeat split.
        - assumption.
        - now symmetry.
    }
    { exists {| world := w1'; runq := rq2'; ref_ctr := vm2_rc |}.
      split.
      - constructor 2 with (vm1 := {| world := vm0_out_w; runq := rq2'; ref_ctr := vm2_rc |}).
        + sauto.
        + sauto.
      - constructor 2 with (vm1 := {| world := w1'; runq := rq3'; ref_ctr := vm2_rc |}).
        + sauto.
        + sauto.
    }
  Qed.

  (* 3/10 *)
  Lemma io_io_swap {pid1 pid2 mb_t1 mb_t2 req1 req2 cont1 cont2} :
    RefOrd.gt pid1 pid2 ->
    swap_ret (h_perform_io pid1 req1) (h_perform_io pid2 req2) ->
    tev_semicommute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @p_io req_t rep_t mb_t1 req1 cont1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_io req_t rep_t mb_t2 req2 cont2 |}.
  Proof.
    intros Hpids12 Hswp vm0 vm4 [vm2 [Hvm1 Hvm2]].
    unfold_vm_step_morph Hvm1.
    simpl in Hvm2.
    unfold_vm_step_morph Hvm2.
    subst.
    (* Run queue: *)
    specialize (RefOrd.gt_not_eq pid1 pid2 Hpids12) as Hpids12_ne.
    assert (Hprocs_ne : {| proc_mb_t := mb_t1; pid := pid1; cont := cont1 req1_rep |} <>
                         {| proc_mb_t := mb_t2; pid := pid2; cont := p_io mb_t2 req2 cont2 |}).
    { intros Habsurd.
      injection Habsurd as H1 H2 H3.
      now rewrite H1 in Hpids12_ne.
    }
    destruct (pick_cons HHvm2_out_pick Hprocs_ne) as [rq1' [Hrq_eq Hrq1']]. subst.
    destruct (pick_two Hvm0_out_pick Hrq1') as [rq2' [rq3' [Hpick_proc2 [Hpick_proc1 Hrq3'b]]]].
    (* World *)
    destruct (Hswp vm0_out_w _ _ _ _ Hvm1_w Hvm2_w) as [w2' [[w1' [Hw1' Hw2']] Hw2'_equiv]].
    (* Build it *)
    exists {| world := w2';
        runq := {| proc_mb_t := mb_t1; pid := pid1; cont := cont1 req1_rep |}
              :: {| proc_mb_t := mb_t2; pid := pid2; cont := cont2 req2_rep |}
              :: rq3';
        ref_ctr := vm0_out_rc
      |}.
    split.
    2:{ simpl. repeat split.
        - apply Hw2'_equiv.
        - rewrite Hrq3'b. sauto.
    }
    { exists {| world := w1';
          runq := {| proc_mb_t := mb_t2; pid := pid2; cont := cont2 req2_rep |} :: rq2';
          ref_ctr := vm0_out_rc
        |}.
      split.
      - constructor 2 with (vm1 := {| world := vm0_out_w; runq := rq2'; ref_ctr := vm0_out_rc |}).
        + sauto.
        + sauto.
      - constructor 2 with (vm1 := {| world := w1';
                                     runq := {| proc_mb_t := mb_t2; pid := pid2; cont := cont2 req2_rep |} :: rq3';
                                     ref_ctr := vm0_out_rc
                                   |}).
        + sauto.
        + sauto.
    }
  Qed.

  (* 4/10 *)
  Lemma exit_spawn_swap `{!IOHandler_exit_spawn} {pid1 pid2 mb_t1 mb_t2 child_mb_t child_cont parent_cont} :
    RefOrd.gt pid1 pid2 ->
    tev_semicommute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @exit req_t rep_t mb_t1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_spawn req_t rep_t mb_t2 child_mb_t child_cont parent_cont |}.
  Proof.
    intros Hpids12 vm0 vm_e [vm1 [Hvm1 Hvm_e]].
    unfold_vm_step_morph Hvm1.
    unfold_vm_step_morph Hvm_e.
    subst. simpl in *.
    (* Run queue *)
    destruct (pick_two Hvm0_out_pick HHvm_e_out_pick) as [rq1' [rq2' [Hrq1' [Hrq2' Hrq2'_equiv]]]].
    (* World *)
    specialize (RefOrd.gt_not_eq pid1 pid2 Hpids12) as Hpids12_ne.
    destruct (h_exit_spawn_swap child_mb_t new_pid Hpids12_ne vm0_out_w Hvm_e_spawn_w) as [w2' [[w1' [Hw1' Hw2']] Hw2'_equiv]]. { sauto. }
    (* Build it *)
    exists {| world := w2';
        runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
              :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
              :: rq2';
        ref_ctr := new_pid_rc
      |}.
    split.
    2:{ simpl. repeat split.
        - assumption.
        - rewrite Hrq2'_equiv. sauto.
    }
    { exists {| world := w1';
           runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
                 :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                 :: rq1';
          ref_ctr := new_pid_rc
        |}.
      split.
      - constructor 2 with (vm1 := {| world := vm0_out_w; runq := rq1'; ref_ctr := Hvm_e_out_rc |}).
        + sauto.
        + unfold exec_proc_morph. simpl. unfold spawn_morph. cbn. simpl. rewrite <-HeqHvm_e_fresh. simpl.
          sauto.
      - constructor 2 with (vm1 :=  {| world := w1';
                                       runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
                                             :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                                             :: rq2';
                                      ref_ctr := new_pid_rc
                                    |}).
        repeat split.
        + sauto.
        + sauto.
    }
  Qed.

  (* 5/10 *)
  Lemma exit_io_swap `{!IOHandler_exit_io} {pid1 pid2 mb_t1 mb_t2 req cont2} :
    RefOrd.gt pid1 pid2 ->
    tev_semicommute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @exit req_t rep_t mb_t1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_io req_t rep_t mb_t2 req cont2 |}.
  Proof.
    intros Hpids vm0 vm_e [vm1 [Hvm1 Hvm_e]].
    unfold_vm_step_morph Hvm1.
    unfold_vm_step_morph Hvm_e.
    subst. simpl in *.
    (* Run queue *)
    destruct (pick_two Hvm0_out_pick HHvm_e_out_pick) as [rq1' [rq2' [Hrq1' [Hrq2' Hrq2'_equiv]]]].
    (* World *)
    specialize (RefOrd.gt_not_eq pid1 pid2 Hpids) as Hpids_ne.
    destruct (h_exit_io_swap Hpids_ne vm0_out_w Hvm_e_out_w vm_e_w tt req_rep ) as [w2' [[w1' [Hw1' Hw2']] Hw2'_equiv]] > [sauto | sauto|].
    (* Build it *)
    exists {| world := w2';
        runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |} :: rq2';
        ref_ctr := Hvm_e_out_rc
      |}.
    split.
    2:{ repeat split.
        - assumption.
        - now rewrite Hrq2'_equiv.
    }
    { exists {| world := w1';
          runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |} :: rq1';
          ref_ctr := Hvm_e_out_rc
        |}.
      split.
      - constructor 2 with (vm1 := {| world := vm0_out_w; runq := rq1'; ref_ctr := Hvm_e_out_rc |}).
        + sauto.
        + sauto.
      - constructor 2 with (vm1 := {| world := w1';
                                     runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |} :: rq2';
                                     ref_ctr := Hvm_e_out_rc
                                   |}).
        + sauto.
        + sauto.
    }
  Qed.

  (* 6/10 *)
  Lemma spawn_io_swap `{!IOHandler_spawn_io} {pid1 pid2 mb_t1 mb_t2 child_mb_t req cont1 cont2 child_cont} :
    RefOrd.gt pid1 pid2 ->
    tev_semicommute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @p_spawn req_t rep_t mb_t1 child_mb_t child_cont cont1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_io req_t rep_t mb_t2 req cont2 |}.
  Proof.
    intros Hpids12 vm0 vm_e [vm1 [Hvm1 Hvm_e]].
    unfold_vm_step_morph Hvm1.
    unfold_vm_step_morph Hvm_e.
    subst. simpl in *.
    (* Run queue *)
    assert (Hpids12_ne : pid1 <> pid2). {
      intros Heq.
      apply RefOrd.ref_compare_eq_iff in Heq.
      unfold RefOrd.gt in Hpids12. now rewrite Heq in Hpids12.
    }
    assert (Hpid1_new : RefOrd.compare_ pid1 new_pid = Lt).
    { exact (Fresh.child_gt_parent _ _ _ _ HeqHvm1_fresh).
    }
    assert (Hpid2_new : RefOrd.compare_ pid2 new_pid = Lt).
    { apply RefOrd.compare_antisymm in Hpids12.
      now specialize (RefOrd.lt_trans Hpids12 Hpid1_new).
    }
    assert (Hnew_pid2_neq : new_pid <> pid2).
    { intros Habsurd.
      apply RefOrd.ref_compare_eq_iff,RefOrd.compare_eq_symm in Habsurd.
      now rewrite Hpid2_new in Habsurd.
    }
    assert (Hne_parent1 : {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 {| mba_pid := new_pid |} |}
                        <> {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req cont2 |}).
    { intros Heq. injection Heq as Hpid_eq Hmb Hcnt.
      now apply Hpids12_ne in Hpid_eq.
    }
    assert (Hne_child1 : {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                       <> {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req cont2 |}).
    { intros Heq. injection Heq as Hpid_eq Hmb Hcnt.
      now apply Hnew_pid2_neq.
    }
    destruct (pick_cons HHvm_e_out_pick Hne_parent1) as [rq_a [Heq_a Hpick_a]].
    subst Hvm_e_out_rq.
    destruct (pick_cons Hpick_a Hne_child1) as [rq_b [Heq_b Hpick_b]].
    subst rq_a.
    destruct (pick_two Hvm0_out_pick Hpick_b) as [rq1' [rq2' [Hrq1' [Hrq2' Hrq2'_equiv]]]].
    (* World *)
    destruct (h_spawn_io_swap child_mb_t req Hnew_pid2_neq vm0_out_w Hvm_e_out_w vm_e_w tt req_rep ) as [w2' [[w1' [Hw1' Hw2']] Hw2'_equiv]]
       > [sauto | sauto|].
    (* Build it *)
    exists {| world := w2';
        runq := {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 {| mba_pid := new_pid |} |}
              :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
              :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |}
              :: rq2';
        ref_ctr := Hvm_e_out_rc
      |}.
    split.
    2:{ simpl. repeat split.
        - assumption.
        - rewrite Hrq2'_equiv.
          eapply Permutation_trans with
            (l' := {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 {| mba_pid := new_pid |} |}
                 :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |}
                 :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                 :: rq_b).
          + apply Permutation.perm_swap.
          + apply perm_skip, Permutation.perm_swap.
    }
    { exists {| world := w1';
          runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |} :: rq1';
          ref_ctr := vm0_out_rc
        |}.
      split.
      - constructor 2 with (vm1 := {| world := vm0_out_w; runq := rq1'; ref_ctr := vm0_out_rc |}).
        + sauto.
        + sauto.
      - constructor 2 with (vm1 := {| world := w1';
                                     runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req_rep |} :: rq2';
                                     ref_ctr := vm0_out_rc
                                   |}).
        + sauto.
        + unfold exec_proc_morph. cbn. unfold spawn_morph, alloc_pid. cbn.
          rewrite <-HeqHvm1_fresh.
          unfold add_ret in Hw2'. cbn in Hw2'.
          eexists. now exists w2'.
    }
  Qed.
End commute.

Global Arguments p_io {_ _ _}.
Global Arguments p_spawn {_ _ _ _}.
Global Arguments exit {_ _ _}.

Notation "'do' V '<-' I ; C" := (p_io (I) (fun V => C))
    (at level 100, I at next level, V name, left associativity) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, I at next level, V name, left associativity) : slot_scope.

Require Import Handlers.Mailbox.

Definition init `(IOHandler_basics) {mb_t} (seed : Program mb_t) :=
  let process := {| pid := []; proc_mb_t := mb_t; cont := seed |} in
  {| world := h_initial;
     ref_ctr := FMap.M.empty _;
     runq := [process]
  |}.

Definition pr {Req Rep} mb_t p (c : @Program Req Rep mb_t) := {| pid := p; proc_mb_t := mb_t; cont := c |}.

Section tests.
  Let req_t := h_request_t mailboxHandler.
  Let rep_t := h_reply_t mailboxHandler.

  Let prog mb_t := @Program req_t rep_t mb_t.

  Let actor1 : prog positive :=
        exit.

  Let actor2 (pid : @Address positive) : prog unit :=
        do _ <- send pid (appmsg 1);
        exit.

  Let system : prog unit :=
        spawn p1 <- actor1;
        spawn _ <- actor2 p1;
        exit.

  Let vm0_1 := init mailboxHandler actor1.

  Goal forall trace vm_e,
      TSMFunGen vm0_1 trace vm_e ->
      CanonicalTrace trace vm0_1 vm_e ->
      trace = [pr _ [] actor1].
  Proof.
    unfold init in *. subst vm0_1.
    intros trace vm_e Htr Hcanon.
    inversion_clear Htr.
    - simpl in H.
  Abort.
End tests.
