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
          `{IOH_b : @IOHandler Request Reply}.

  Let World := @h_state _ _ IOH_b.

  Let Hequiv_w := @h_setoid _ _ IOH_b.

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

  (** ** Canonical order *)

  Definition vmte_canon_rel (a b : Process) :=
    (* Order of events is canonical when pid a >= pid b: *)
    match RefOrd.compare_ (pid a) (pid b) with
    | Lt => False
    | _ => True
    end.

  Lemma vmte_canon_rel_dec a b : Decidable.decidable (vmte_canon_rel a b).
  Proof.
    unfold Decidable.decidable, vmte_canon_rel.
    sauto.
  Qed.

  Lemma vmte_canon_rel_total a b : vmte_canon_rel a b \/ vmte_canon_rel b a.
  Proof.
    unfold Decidable.decidable, vmte_canon_rel.
    remember (RefOrd.compare_ (pid a) (pid b)) as ord.
    destruct ord.
    - now left.
    - right. symmetry in Heqord. apply RefOrd.compare_antisymm in Heqord.
      now rewrite Heqord.
    - now left.
  Qed.

  Global Instance vmevCanonOrder : CanonicalOrder vmte_canon_rel :=
    { canon_rel_dec := vmte_canon_rel_dec;
      canon_rel_total := vmte_canon_rel_total;
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
    destruct x as [w rq rc inv].
    destruct x' as [w' rq' rc' inv'].
    destruct rq as [|rq_ rq_rest]; simpl in *;
      destruct H as [Hw [Hrc Hperm]].
    - exists None. split.
      + destruct rq' as [|rq'_ rq'_rest]; try easy.
        now apply Permutation_nil in Hperm.
      + now subst.
    - destruct y as [[proc vm2]|]; try easy.
      destruct vm2 as [w2 rq2 rc2 inv2].
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
    destruct vm0 as [w0 rq0 rc0 inv0].
    destruct vm1 as [w1 rq1 rc1 inv1].
    simpl in H.
    destruct rq0 as [|f r].
    - exfalso. discriminate.
    - assumption.
  Qed.

  (** ** Operations with the world *)

  Program Definition lift_w_ret {Ret : Type} `{Hequiv_r : Setoid Ret}
    (w_morph : @MFunRet Ret World World Hequiv_r Hequiv_w Hequiv_w) : @MFunRet Ret VM VM Hequiv_r vm_setoid vm_setoid :=
    {| morphism vm1 ret :=
        let (ret, vm2) := ret in
        match vm1, vm2 with
          {| world := w1; runq := rq1; ref_ctr := rc1 |},
          {| world := w2; runq := rq2; ref_ctr := rc2 |} =>
            w1 ~[w_morph]~> (ret, w2) /\
            rq1 = rq2 /\
            rc1 = rc2
        end;
    |}.
  Next Obligation.
    destruct x as [w1 rq1 rc1].
    destruct x' as [w1' rq1' rc1'].
    destruct v as [w2 rq2 rc2].
    destruct H as [Hw [Hrc Hrq]].
    destruct H0 as [Hw12 [Hrc12 Hrq12]].
    subst.
    apply morphism_covariance with (x' := w1') in Hw12; [|now rewrite Hw].
    destruct Hw12 as [[ret' w2'] [Hw12' H2]].
    destruct H2 as [Hret Hw2].
    exists (ret', {| world := w2'; runq := rq1'; ref_ctr := rc1' |}).
    repeat split; try assumption.
    - apply Hrc.
  Qed.

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
      (child_mb_t : Set) (child_cont : Program child_mb_t)
      (parent : Pid) (parent_mb_t : Set)
      (parent_cont : @Address child_mb_t -> Program parent_mb_t).

    (** Allocate a new pid for a process and add it to the VM.
        Update the parent process (which should be scheduled out),
        and add it to the VM too. Does not change the world. *)
    Definition alloc_pid (vm : VM) : Pid * VM.
    Proof.
      destruct vm as [w rq rc inv_valid].
      destruct (Fresh.make parent rc) as [new rc'].
      set (addr := mkAddress child_mb_t new).
      set (rq' :=
             {| pid := parent; proc_mb_t := parent_mb_t; cont := parent_cont addr |} ::
             {| pid := new; proc_mb_t := child_mb_t; cont := child_cont |} ::
             rq).
      exact (new, {| world := w; runq := rq'; ref_ctr := rc' |}).
    Defined.

    Lemma alloc_pid_covariance
      (vm vm' : VM)
      (Hvm' : vm == vm') :
      @equiv _ (pair_setoid' (eq_setoid _) vm_setoid) (alloc_pid vm) (alloc_pid vm').
    Proof.
      destruct vm as [w1 rq1 rc1 inv1].
      destruct vm' as [w1' rq1' rc1' inv1'].
      unfold alloc_pid.
      simpl in Hvm'. destruct Hvm' as [Hw [Hrc Hrq]].
      (* Ref counters: *)
      apply Fresh.make_morph with (parent := parent) in Hrc.
      destruct (Fresh.make parent rc1) as [new_pid rc2].
      destruct (Fresh.make parent rc1') as [new_pid' rc2'].
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

    (** Allocate a new pid for a process and add it to the VM.
        Update the parent process (which should be scheduled out),
        and add it to the VM too. *)
    Definition spawn_morph (vm0 vm2 : VM) : Prop :=
      let (new_pid, vm1) := alloc_pid vm0 in
      exists2 w2 : World,
          (world vm1) ~[h_spawn new_pid child_mb_t]~> w2 &
          vm2 = vm1<|world := w2|>.

    Program Definition spawn : MFun VM VM :=
      {| morphism := spawn_morph;
      |}.
    Next Obligation.
      rename x into vm0. rename x' into vm0'. rename y into vm. rename H into Hvm0. rename H0 into Hvm.
      unfold spawn_morph in *.
      specialize (alloc_pid_covariance vm0 vm0' Hvm0) as Hvm1'.
      destruct (alloc_pid vm0) as [new_pid vm1].
      destruct (alloc_pid vm0') as [new_pid' vm1'].
      destruct Hvm1' as [Hnew_pid Hvm1']. simpl in Hnew_pid.
      destruct Hvm as [w2 Hw2 Hvm2].
      subst.
      destruct vm1 as [w1 rq1 rc1].
      destruct vm1' as [w1' rq1' rc1'].
      destruct Hvm1' as [Hw1 [Hrc1 Hrq1]].
      morph_shift (h_spawn new_pid' child_mb_t) w1'.
      exists {| world := w2'; runq := rq1'; ref_ctr := rc1' |}.
      split.
      - now exists w2'.
      - easy.
    Qed.
  End spawn.

  Section io.
    Context
      (pd : Pid) (mb_t : Set) (req : Request)
      (cnt : Reply req -> Program mb_t).

    Definition perform_io_morph (vm1 vm2 : VM) : Prop :=
      let (w1, rq1, rc1) := vm1 in
      let (w2, rq2, rc2) := vm2 in
      exists (rep : Reply req),
        w1 ~[h_perform_io pd req]~> (rep, w2) /\
          rc2 = rc1 /\
          rq2 = {| pid := pd; proc_mb_t := mb_t; cont := cnt rep |} :: rq1.

    Program Definition perform_io : MFun VM VM :=
      {| morphism := perform_io_morph;
      |}.
    Next Obligation.
      destruct x as [w1 rq1 rc1].
      destruct x' as [w1' rq1' rc1'].
      destruct y as [w2 rq2 rc2].
      cbn in H. destruct H as [Hw1 [Hrc1 Hrq1]].
      cbn in H0. destruct H0 as [rep [Hhandler [Hrc13 Hrq13]]].
      apply morphism_covariance with (x' := w1') in Hhandler; [|assumption].
      destruct Hhandler as [[rep' w2'] [Hw2' [Hrep Hw2_eqiuv']]].
      simpl in Hrep.
      subst.
      exists {| world := w2';
           runq := {| pid := pd; proc_mb_t := mb_t; cont := cnt rep' |} :: rq1';
           ref_ctr := rc1'
        |}.
      split.
      - exists rep'. easy.
      - repeat split.
        + easy.
        + apply Hrc1.
        + now apply perm_skip.
    Qed.
  End io.

  Section exit.
    Context (pid : Pid).

    Definition terminate_morph (vm1 vm2 : VM) : Prop :=
      vm1 ~[lift_w (h_terminate true pid)]~> vm2.

    Program Definition terminate : MFun VM VM :=
      {| morphism  := terminate_morph
      |}.
    Next Obligation.
      destruct x as [w1 rq1 rc1 inv1].
      destruct x' as [w1' rq1' rc1' inv1'].
      destruct y as [w2 rq2 rc2 inv2].
      cbn in H. destruct H as [Hw1 [Hrc1 Hrq1]].
      cbn in H0. destruct H0 as [Hterm [Hrq13 Hrc13]].
      morph_shift (h_terminate true pid) w1'.
      subst.
      now exists {| world := w2'; runq := rq1'; ref_ctr := rc1' |}.
    Qed.
  End exit.

  Definition exec_proc_morph (proc : Process) (vm1 vm2 : VM) : Prop :=
    let pid := pid proc in
    let proc_mb_t := proc_mb_t proc in
    match cont proc with
    | exit _ =>
        vm1 ~[terminate pid]~> vm2
    | p_io _ req cont =>
        vm1 ~[perform_io pid proc_mb_t req cont]~> vm2
    | @p_spawn _ child_mb_t child_cont parent_cont =>
        vm1 ~[spawn child_mb_t child_cont pid proc_mb_t parent_cont]~> vm2
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
    destruct prog; unfold exec_proc_morph in Hvm2;
      try now apply morphism_covariance with (x' := vm0') in Hvm2.
    contradiction.
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

Section tests.
  Context {Request : Type} {Reply : Request -> Type}
          `{IO_b : @IOHandler Request Reply}.

  Goal forall (vm1 vm2 : VM), vm1 = vm2 -> False.
    intros vm1 vm2 H.
    dvm vm1 vm2.
  Abort.
End tests.

Section canned.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH_b : @IOHandler Request Reply}.

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
  | @morphism _ _ _ _ (terminate _) _ _ =>
      unfold terminate in $id;
      destruct $new_hyp as [_vt_exit $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (perform_io _ _ _ _) _ _ =>
      unfold perform_io in $id;
      destruct $new_hyp as [_vt_io $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (spawn _ _ _ _ _) _ _ =>
      unfold spawn_morph in $id;
      destruct $new_hyp as [_vt_spawn $id];
      unfold_exec_proc_morph id
  | @morphism _ _ _ _ (perform_io _ _ ?req _) _ _ =>
      let rep := fresh_id (String.app (maybe_hyp_to_string req "") "_rep") in
      unfold perform_io in $id;
      destruct $new_hyp as [$rep [$hworld [$hrq $hrc]]]
  | @morphism _ _ _ _ (terminate _) _ _ =>
      unfold terminate in $id;
      cbn in $id;
      unfold_exec_proc_morph id
  | perform_io_morph _ _ ?req _ _ _ _ =>
      let rep := fresh_id (String.app (maybe_hyp_to_string req "") "_rep") in
      destruct $new_hyp as [$rep [$hworld [$hrq $hrc]]]
  | terminate_morph _ _ _ _ =>
      unfold terminate_morph in $id;
      cbn in $id;
      unfold_exec_proc_morph id
  | _ /\ _ /\ _ =>
      destruct $new_hyp as [$hworld [$hrq $hrc]]
  | @morphism _ _ _ _ (spawn _ _ _ _ _) _ _ =>
      (* The spawn step of [exec_proc_morph] is stated via the [spawn]
         MFun on the sigma type of VMs with a valid parent pid; unfold
         it back into [do_spawn] and retry. *)
      unfold spawn in $id;
      cbn in $id;
      unfold_exec_proc_morph id
  | spawn_morph ?_child_mb_t' ?_child' ?_parent' ?_parent_mb_t' ?_parent_cont' ?_vm0' ?_vm_end =>
      let new_pid := fresh_id "new_pid" in
      let new_rc := fresh_id "new_pid_rc" in
      let hvalid := fresh_id "Hnew_pid_rc_valid" in
      let hmake := fresh_id "Hmake_pid" in
      let w2 := fresh_id (String.app hyp_prefix "_spawn_w") in
      let heq_vm := fresh_id (String.app hyp_prefix "_eq_vm") in
      let fresh_make_result := fresh_id (String.app hyp_prefix "_fresh") in
      unfold spawn_morph in $id;
      cbn in $id;
      lazy_match! Constr.type (Control.hyp id) with
      | context [Fresh.make ?parent_mw ?rc_mw] =>
          remember (Fresh.make $parent_mw $rc_mw) as fresh_make_result;
          destruct fresh_make_result as [$new_pid $new_rc]
      end;
      let new_hyp := Control.hyp id in
      destruct $new_hyp as [$w2 $hworld $heq_vm];
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
  let valid := fresh_id (String.app "H" (String.app prefix "_valid")) in
  let inv := fresh_id (String.app "H" (String.app (String.app prefix "_rc") "_valid")) in
  destruct (Fresh.make $pid $rc) as [$new_pid $new_rc].

Ltac2 Notation "unfold_alloc_pid" pid(constr) rc(constr) new(seq("as", ident)) := unfold_alloc_pid pid rc new.

Notation "'P<' T > A @ C " := {| pid := A; proc_mb_t := T; cont := C |} (at level 100).

Section commute.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler Request Reply}.

  Let req_t := h_request_t IOH.
  Let rep_t := h_reply_t IOH.
  Let prog_t := @Program req_t rep_t.

  Ltac2 solve_alloc_pid () :=
    simpl;
    lazy_match! goal with
      [ h_new : Fresh.make ?pid ?rc0 = (?new, ?rc1) |- context [Fresh.make ?pid ?rc0] ] =>
        let h := Control.hyp h_new in
        rewrite (Fresh.make $pid $rc0 $new)
    end.

  Ltac2 Notation "solve_alloc_pid" := solve_alloc_pid ().

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
  Lemma spawn_spawn_swap {pid1 pid2 mb_t1 mb_t2 child_mb_t1 child_mb_t2 child1 child2 cont1 cont2} :
    RefOrd.gt pid1 pid2 ->
    ts_events_swap
      {| pid := pid1; proc_mb_t := mb_t1; cont := @p_spawn req_t rep_t mb_t1 child_mb_t1 child1 cont1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_spawn req_t rep_t mb_t2 child_mb_t2 child2 cont2 |}.
  Proof.
    intros Hpids12.
    (* Unfold the original path: *)
    unfold ts_events_swap, swappable, exists_equiv.
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
    { now apply Fresh.child_gt_parent in Heqfresh_make_result.
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
    { apply (Fresh.different_parents_children pid1 pid2 new_pid new_pid0 Hpids12_ne Heqfresh_make_result Heqfresh_make_result0).
    }
    assert (Hnew_pids_gt : RefOrd.gt new_pid new_pid0). {
      apply (Fresh.gt_parents_children pid1 pid2 new_pid new_pid0 Hpids12 Heqfresh_make_result Heqfresh_make_result0).
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
    symmetry in Heqfresh_make_result. symmetry in Heqfresh_make_result0.
    swap_make ().
    (* Build the new world *)
    simpl in Hvm2_w. simpl in Hvm4_w.
    destruct (h_spawn_commutativity new_pid new_pid0 child_mb_t1 child_mb_t2 Hnew_pids_gt vm0_out_w Hvm4_spawn_w) as [w2' [Hw2' Hw2'_equiv]].
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
        + unfold exec_proc_morph. cbn. unfold spawn_morph,alloc_pid.
          rewrite Hnew_pid1'. now exists w1'.
      - simpl.
        constructor 2 with (vm1 := {| world := w1';
                                     runq := {| proc_mb_t := mb_t2; pid := pid2; cont := cont2 {| mba_pid := new_pid0 |} |}
                                           :: {| proc_mb_t := child_mb_t2; pid := new_pid0; cont := child2 |}
                                           :: rq3';
                                     ref_ctr := rc2'
                                   |}).
        + sauto.
        + unfold exec_proc_morph. cbn. unfold spawn_morph,alloc_pid.
          rewrite Hnew_pid2'. now exists w2'.
    }
  Qed.

  (* 2/10 *)
  Lemma exit_exit_commute {pid1 pid2 mb_t1 mb_t2} :
    pid1 <> pid2 ->
    (forall rc (v1 : is_valid_pid pid1 rc)
               (v2 : is_valid_pid pid2 rc),
       commute (h_terminate true pid1 rc v1) (h_terminate true pid2 rc v2)) ->
    ts_event_commute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @exit req_t rep_t mb_t1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @exit req_t rep_t mb_t2 |}.
  Proof.
    intros Hpids Hw_comm vm0 vm2.
    split; intros [vm1 [Hvm1 Hvm2]].
    - unfold_vm_step_morph Hvm1. simpl in Hvm2.
      unfold_vm_step_morph Hvm2.
      unfold_schedule_out Hvm0_out.
      unfold_schedule_out HHvm2_out.
      subst.
      (* World: the validity witnesses are taken from the two
         destructed steps so that the terms match. *)
      lazy_match! goal with
      | [ _h1 : context [ h_terminate true pid1 ?_rc1 ?v1 ],
          _h2 : context [ h_terminate true pid2 ?_rc2 ?v2 ] |- _ ] =>
          destruct (Hw_comm vm2_rc $v1 $v2 vm0_out_w vm2_w) as [Hw1 Hw2]
      end.
      destruct Hw1 as [w2' [[w1' [Hw1' Hw2']] Hw1w1']] > [eexists; split; eassumption|].
      (* Run queue *)
      destruct (pick_two Hvm0_out_pick HHvm2_out_pick) as [rq1' [rq2' [Hrq1' [Hrq2' Hrq2'equiv]]]].
      (* The invariant *)
      assert (inv1' : Forall (proc_valid_pid vm2_rc) rq1') by solve_rc_invariant.
      assert (inv2' : Forall (proc_valid_pid vm2_rc) rq2') by solve_rc_invariant.
      (* Build VM *)
      exists ({| world := w2'; runq := rq2'; ref_ctr := vm2_rc; inv_valid_pids := inv2' |}).
      split.
      + exists ({| world := w1'; runq := rq1'; ref_ctr := vm2_rc; inv_valid_pids := inv1' |}). split.
        * simpl. solve_vm_step () >
          [ destruct vm0_rq as [|x xs] >
            [ ltac1:(exfalso; inversion Hrq1')
            | unfold schedule_out; cbn;
              split > [exact Hrq1' | split > [reflexivity | reflexivity]] ]
          | cbn;
            split > [ eapply h_terminate_morph_pi; eassumption
                    | split > [reflexivity | reflexivity] ] ].
        * simpl. solve_vm_step () >
          [ destruct rq1' as [|x xs] >
            [ ltac1:(exfalso; inversion Hrq2')
            | unfold schedule_out; cbn;
              split > [exact Hrq2' | split > [reflexivity | reflexivity]] ]
          | cbn;
            split > [ eapply h_terminate_morph_pi; eassumption
                    | split > [reflexivity | reflexivity] ] ].
      + simpl. repeat split.
        * assumption.
        * now apply Permutation_sym.
    - Std.rename [(@pid1, @pid2); (@pid2, @pid1); (@mb_t1, @mb_t2); (@mb_t2, @mb_t1)].
      (* Carbon copy of the above, except we use Hw2 hypothesis instead of Hw1 *)
      unfold_vm_step_morph Hvm1. simpl in Hvm2.
      unfold_vm_step_morph Hvm2.
      unfold_schedule_out Hvm0_out.
      unfold_schedule_out HHvm2_out.
      subst.
      (* World: *)
      (* [Std.rename] swapped the roles of pid1/pid2 (and mb_t1/mb_t2):
         [Hw_comm] still expects the validity of the *first* event's pid
         in its [v1] argument, which is now named pid2. *)
      lazy_match! goal with
      | [ _h1 : context [ h_terminate true pid2 ?_rc1 ?v1 ],
          _h2 : context [ h_terminate true pid1 ?_rc2 ?v2 ] |- _ ] =>
          destruct (Hw_comm vm2_rc $v1 $v2 vm0_out_w vm2_w) as [Hw1 Hw2]
      end.
      destruct Hw2 as [w2' [[w1' [Hw1' Hw2']] Hw1w1']] > [eexists; split; eassumption|].
      (* Run queue *)
      destruct (pick_two Hvm0_out_pick HHvm2_out_pick) as [rq1' [rq2' [Hrq1' [Hrq2' Hrq2'equiv]]]].
      (* The invariant *)
      assert (inv1' : Forall (proc_valid_pid vm2_rc) rq1') by solve_rc_invariant.
      assert (inv2' : Forall (proc_valid_pid vm2_rc) rq2') by solve_rc_invariant.
      (* Build VM *)
      exists ({| world := w2'; runq := rq2'; ref_ctr := vm2_rc; inv_valid_pids := inv2' |}).
      split.
      + exists ({| world := w1'; runq := rq1'; ref_ctr := vm2_rc; inv_valid_pids := inv1' |}). split.
        * simpl. solve_vm_step () >
          [ destruct vm0_rq as [|x xs] >
            [ ltac1:(exfalso; inversion Hrq1')
            | unfold schedule_out; cbn;
              split > [exact Hrq1' | split > [reflexivity | reflexivity]] ]
          | cbn;
            split > [ eapply h_terminate_morph_pi; eassumption
                    | split > [reflexivity | reflexivity] ] ].
        * simpl. solve_vm_step () >
          [ destruct rq1' as [|x xs] >
            [ ltac1:(exfalso; inversion Hrq2')
            | unfold schedule_out; cbn;
              split > [exact Hrq2' | split > [reflexivity | reflexivity]] ]
          | cbn;
            split > [ eapply h_terminate_morph_pi; eassumption
                    | split > [reflexivity | reflexivity] ] ].
      + simpl. repeat split.
        * assumption.
        * now apply Permutation_sym.
  Qed.

  (* 3/10 *)
  Lemma io_io_commute {pid1 pid2 mb_t1 mb_t2 req1 req2 cont1 cont2} :
    pid1 <> pid2 ->
    (forall rc (v1 : is_valid_pid pid1 rc)
               (v2 : is_valid_pid pid2 rc),
       commute_ret (h_perform_io pid1 rc v1 req1) (h_perform_io pid2 rc v2 req2)) ->
    ts_event_commute
      {| pid := pid1; proc_mb_t := mb_t1; cont := @p_io req_t rep_t mb_t1 req1 cont1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_io req_t rep_t mb_t2 req2 cont2 |}.
  Proof.
    intros Hpids Hcomm vm0 vm4.
    split; intros [vm2 [Hvm1 Hvm2]].
  - unfold_vm_step_morph Hvm1.
    simpl in Hvm2.
    unfold_vm_step_morph Hvm2.
    unfold_schedule_out Hvm0_out.
    unfold_schedule_out HHvm2_out.
    subst vm0_out_w.
    subst Hvm2_out_w.
    subst vm0_out_rc.
    subst Hvm2_out_rc.
    subst vm2_rq.
    subst vm2_rc.
    subst vm4_rc.
    subst vm4_rq.
    (* The continuation process left in the queue by the first I/O
       cannot be the process scheduled out second (their pids differ): *)
    assert (Hne :
      {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
      <> {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |}).
    { intros Heq. injection Heq as Hpid_eq Hmb Hcnt. now apply Hpids. }
    destruct (pick_cons HHvm2_out_pick Hne) as [rq_a [Heq_a Hpick_a]].
    subst Hvm2_out_rq.
    destruct (pick_two Hvm0_out_pick Hpick_a)
      as [rq2' [rq3' [Hpick_proc2 [Hpick_proc1 Hrq3'equiv]]]].
    (* Worlds and replies: the two handlers commute. *)
    lazy_match! goal with
    | [ _h1 : context [ h_perform_io pid1 ?_rc1 ?v1 req1 ],
        _h2 : context [ h_perform_io pid2 ?_rc2 ?v2 req2 ] |- _ ] =>
        destruct (Hcomm vm0_rc $v1 $v2 vm0_w vm2_w vm4_w req1_rep req2_rep) as [Hl Hr]
    end.
    specialize (Hl Hvm1_w Hvm2_w).
    unfold exists_equiv in Hl.
    destruct Hl as [w_fin [[w_mid [Hg_first Hf_second]] Hw4fin]].
    (* Invariant proofs for the queues of the swapped run (the
       reference counter is unchanged by I/O steps): *)
    assert (INV_RQ2' : Forall (proc_valid_pid vm0_rc) rq2').
    { eapply pick_forall_rest > [exact vm0_pids_valid | exact Hpick_proc2]. }
    assert (INV_MID : Forall (proc_valid_pid vm0_rc)
      ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq2')).
    { constructor >
        [ exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
                   {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |} rq2'
                   vm0_pids_valid Hpick_proc2)
        | exact INV_RQ2']. }
    assert (INV_RQ3' : Forall (proc_valid_pid vm0_rc) rq3').
    { eapply pick_forall_rest > [exact INV_RQ2' | exact Hpick_proc1]. }
    assert (Hval1 : is_valid_pid pid1 vm0_rc).
    { exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
               {| pid := pid1; proc_mb_t := mb_t1; cont := p_io mb_t1 req1 cont1 |} vm0_out_rq
               vm0_pids_valid Hvm0_out_pick). }
    assert (INV_FIN : Forall (proc_valid_pid vm0_rc)
      ({| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
       :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { constructor > [exact Hval1 |
      constructor > [ exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
                             {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |} rq2'
                             vm0_pids_valid Hpick_proc2)
                    | exact INV_RQ3']]. }
    exists {| world := w_fin;
             runq := {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
                      :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3';
             ref_ctr := vm0_rc;
             inv_valid_pids := INV_FIN |}.
    split.
    simpl.
    exists {| world := w_mid;
             runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq2';
             ref_ctr := vm0_rc;
             inv_valid_pids := INV_MID |}.
    split.
    vm_step_some {| world := vm0_w; runq := rq2'; ref_ctr := vm0_rc;
                    inv_valid_pids := INV_RQ2' |}.
    destruct vm0_rq as [|x xs] >
      [ ltac1:(exfalso; inversion Hpick_proc2)
      | unfold schedule_out; cbn;
        split > [exact Hpick_proc2 | split > [reflexivity | reflexivity]] ].
    unfold exec_proc_morph. cbn. unfold perform_io. cbn. unfold do_io. cbn.
    exists req2_rep.
    split > [ (ltac1:(eapply h_perform_io_morph_pi; exact Hg_first)) | split ].
    reflexivity.
    reflexivity.
    assert (Hpick_proc1' :
      Pick ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq2')
           {| pid := pid1; proc_mb_t := mb_t1; cont := p_io mb_t1 req1 cont1 |}
           ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { apply pick_cons_rev. exact Hpick_proc1. }
    assert (INV_PICK1 : Forall (proc_valid_pid vm0_rc)
      ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { constructor > [ exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
                             {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |} rq2'
                             vm0_pids_valid Hpick_proc2)
                    | exact INV_RQ3']. }
    vm_step_some {| world := w_mid;
                    runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3';
                    ref_ctr := vm0_rc;
                    inv_valid_pids := INV_PICK1 |}.
    unfold schedule_out. cbn. split > [exact Hpick_proc1' | split].
    reflexivity.
    reflexivity.
    unfold exec_proc_morph. cbn. unfold perform_io. cbn. unfold do_io. cbn.
    exists req1_rep.
    split > [ (ltac1:(eapply h_perform_io_morph_pi; exact Hf_second)) | split ].
    reflexivity.
    reflexivity.
    assert (Hperm :
      ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |}
       :: {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |} :: rq_a)
      =p=
      ({| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
       :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { eapply Permutation_trans.
      apply Permutation.perm_swap.
      repeat (apply perm_skip).
      apply Permutation_sym.
      exact Hrq3'equiv. }
    split > [exact Hw4fin | split > [reflexivity | exact Hperm]].
  - (* The following is a carbon copy of the above, except that the
       world commutativity uses the other disjunct of [commute_ret] *)
    Std.rename [(@pid1, @pid2); (@pid2, @pid1);
                (@mb_t1, @mb_t2); (@mb_t2, @mb_t1);
                (@req1, @req2); (@req2, @req1);
                (@cont1, @cont2); (@cont2, @cont1)].
    unfold_vm_step_morph Hvm1.
    simpl in Hvm2.
    unfold_vm_step_morph Hvm2.
    unfold_schedule_out Hvm0_out.
    unfold_schedule_out HHvm2_out.
    subst vm0_out_w.
    subst Hvm2_out_w.
    subst vm0_out_rc.
    subst Hvm2_out_rc.
    subst vm2_rq.
    subst vm2_rc.
    subst vm4_rc.
    subst vm4_rq.
    (* The continuation process left in the queue by the first I/O
       cannot be the process scheduled out second (their pids differ): *)
    assert (Hne :
      {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
      <> {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |}).
    { intros Heq. injection Heq as Hpid_eq Hmb Hcnt. now apply Hpids. }
    destruct (pick_cons HHvm2_out_pick Hne) as [rq_a [Heq_a Hpick_a]].
    subst Hvm2_out_rq.
    destruct (pick_two Hvm0_out_pick Hpick_a)
      as [rq2' [rq3' [Hpick_proc2 [Hpick_proc1 Hrq3'equiv]]]].
    (* Worlds and replies: the two handlers commute. *)
    lazy_match! goal with
    | [ _h1 : context [ h_perform_io pid2 ?_rc1 ?v1 req2 ],
        _h2 : context [ h_perform_io pid1 ?_rc2 ?v2 req1 ] |- _ ] =>
        destruct (Hcomm vm0_rc $v1 $v2 vm0_w vm2_w vm4_w req2_rep req1_rep) as [Hl Hr]
    end.
    specialize (Hr Hvm1_w Hvm2_w).
    unfold exists_equiv in Hr.
    destruct Hr as [w_fin [[w_mid [Hg_first Hf_second]] Hw4fin]].
    (* Invariant proofs for the queues of the swapped run (the
       reference counter is unchanged by I/O steps): *)
    assert (INV_RQ2' : Forall (proc_valid_pid vm0_rc) rq2').
    { eapply pick_forall_rest > [exact vm0_pids_valid | exact Hpick_proc2]. }
    assert (INV_MID : Forall (proc_valid_pid vm0_rc)
      ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq2')).
    { constructor >
        [ exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
                   {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |} rq2'
                   vm0_pids_valid Hpick_proc2)
        | exact INV_RQ2']. }
    assert (INV_RQ3' : Forall (proc_valid_pid vm0_rc) rq3').
    { eapply pick_forall_rest > [exact INV_RQ2' | exact Hpick_proc1]. }
    assert (Hval1 : is_valid_pid pid1 vm0_rc).
    { exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
               {| pid := pid1; proc_mb_t := mb_t1; cont := p_io mb_t1 req1 cont1 |} vm0_out_rq
               vm0_pids_valid Hvm0_out_pick). }
    assert (INV_FIN : Forall (proc_valid_pid vm0_rc)
      ({| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
       :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { constructor > [exact Hval1 |
      constructor > [ exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
                             {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |} rq2'
                             vm0_pids_valid Hpick_proc2)
                    | exact INV_RQ3']]. }
    exists {| world := w_fin;
             runq := {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
                      :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3';
             ref_ctr := vm0_rc;
             inv_valid_pids := INV_FIN |}.
    split.
    simpl.
    exists {| world := w_mid;
             runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq2';
             ref_ctr := vm0_rc;
             inv_valid_pids := INV_MID |}.
    split.
    vm_step_some {| world := vm0_w; runq := rq2'; ref_ctr := vm0_rc;
                    inv_valid_pids := INV_RQ2' |}.
    destruct vm0_rq as [|x xs] >
      [ ltac1:(exfalso; inversion Hpick_proc2)
      | unfold schedule_out; cbn;
        split > [exact Hpick_proc2 | split > [reflexivity | reflexivity]] ].
    unfold exec_proc_morph. cbn. unfold perform_io. cbn. unfold do_io. cbn.
    exists req2_rep.
    split > [ (ltac1:(eapply h_perform_io_morph_pi; exact Hg_first)) | split ].
    reflexivity.
    reflexivity.
    assert (Hpick_proc1' :
      Pick ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq2')
           {| pid := pid1; proc_mb_t := mb_t1; cont := p_io mb_t1 req1 cont1 |}
           ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { apply pick_cons_rev. exact Hpick_proc1. }
    assert (INV_PICK1 : Forall (proc_valid_pid vm0_rc)
      ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { constructor > [ exact (pick_forall_elem (proc_valid_pid vm0_rc) vm0_rq
                             {| pid := pid2; proc_mb_t := mb_t2; cont := p_io mb_t2 req2 cont2 |} rq2'
                             vm0_pids_valid Hpick_proc2)
                    | exact INV_RQ3']. }
    vm_step_some {| world := w_mid;
                    runq := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3';
                    ref_ctr := vm0_rc;
                    inv_valid_pids := INV_PICK1 |}.
    unfold schedule_out. cbn. split > [exact Hpick_proc1' | split].
    reflexivity.
    reflexivity.
    unfold exec_proc_morph. cbn. unfold perform_io. cbn. unfold do_io. cbn.
    exists req1_rep.
    split > [ (ltac1:(eapply h_perform_io_morph_pi; exact Hf_second)) | split ].
    reflexivity.
    reflexivity.
    assert (Hperm :
      ({| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |}
       :: {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |} :: rq_a)
      =p=
      ({| pid := pid1; proc_mb_t := mb_t1; cont := cont1 req1_rep |}
       :: {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 req2_rep |} :: rq3')).
    { eapply Permutation_trans.
      apply Permutation.perm_swap.
      repeat (apply perm_skip).
      apply Permutation_sym.
      exact Hrq3'equiv. }
    split > [exact Hw4fin | split > [reflexivity | exact Hperm]].
  Qed.

  (* 4/10 *)
  Lemma exit_spawn_commute {pid1 pid2 mb_t1 mb_t2 child_mb_t child_cont parent_cont} :
    pid1 <> pid2 ->
    ts_event_commute_ctx
      (fun vm => is_valid_pid pid1 (ref_ctr vm) /\
              is_valid_pid pid2 (ref_ctr vm))
      {| pid := pid1; proc_mb_t := mb_t1; cont := @exit req_t rep_t mb_t1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_spawn req_t rep_t mb_t2 child_mb_t child_cont parent_cont |}.
  Proof.
    intros Hpid12 vm0 vm4 [Hpid1_valid Hpid2_valid].
    unfold ts_event_commute_ctx, commute_ctx, commute_def, exists_equiv.
    split; intros [vm2 [Hvm1 Hvm2]].
    - (* exit -> spawn *)
      unfold_vm_step_morph Hvm1.
      simpl in Hvm2.
      unfold_vm_step_morph Hvm2.
      injection Hvm2_eq_vm as F1 F2 F3.
      subst vm4_w vm4_rq vm4_rc.
      clear Hvm2_eq_vm F1 F2 F3.
      unfold_schedule_out Hvm0_out.
      unfold_schedule_out HHvm2_out.
      cbn in Hpid1_valid, Hpid2_valid.
      subst vm0_out_w.
      subst Hvm2_out_w.
      subst vm0_out_rc.
      subst Hvm2_out_rc.
      subst.
      (* Run queue *)
      destruct (pick_two Hvm0_out_pick HHvm2_out_pick)
        as [rq2' [rq3' [Hpick_proc2 [Hpick_proc1 Hrq3'equiv]]]].
      (* pid1 is distinct from the spawned pid *)
      assert (Hne : pid1 <> new_pid).
      { apply not_eq_sym.
        exact (Fresh.make_valid_not_equal pid2 pid1 new_pid vm2_rc new_pid_rc
                 Hpid1_valid Hmake_pid). }
      (* The exit and the spawn commute at the level of the VM's own
         operations: the law is applied to a synthetic two-step run
         with an empty run queue, reusing the allocation equation and
         the world effects of the destructed run. *)
      ltac1:(pose proof vm4_pids_valid as HI4).
      ltac1:(inversion HI4 as [|? ? HI_p2s HI4r]).
      ltac1:(inversion HI4r as [|? ? HI_c2s _]).
      assert (Hleg1 :
        @morphism _ _ _ _ (terminate_vm pid1)
          {| world := vm0_w; runq := []; ref_ctr := vm2_rc;
             inv_valid_pids := Forall_nil (proc_valid_pid vm2_rc) |}
          {| world := vm2_w; runq := []; ref_ctr := vm2_rc;
             inv_valid_pids := Forall_nil (proc_valid_pid vm2_rc) |}).
      { unfold terminate_vm, totalize. cbn.
        exists Hpid1_valid.
        unfold terminate. cbn. unfold do_exit. cbn.
        split.
        - ltac1:(eapply h_terminate_morph_pi; eassumption).
        - split > [reflexivity | reflexivity]. }
      assert (Hleg2 :
        @morphism _ _ _ _
          (spawn_vm child_mb_t child_cont pid2 mb_t2 parent_cont)
          {| world := vm2_w; runq := []; ref_ctr := vm2_rc;
             inv_valid_pids := Forall_nil (proc_valid_pid vm2_rc) |}
          {| world := Hvm2_spawn_w;
             runq :=
               {| pid := pid2; proc_mb_t := mb_t2;
                  cont := parent_cont {| mba_pid := new_pid |} |}
               :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                  :: [];
             ref_ctr := new_pid_rc;
             inv_valid_pids :=
               Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}).
      { unfold spawn_vm, totalize. cbn.
        exists Hpid2_valid.
        unfold spawn. cbn. unfold do_spawn. cbn.
        rewrite (Fresh.make_valid_eq pid2 vm2_rc new_pid new_pid_rc Hmake_pid). cbn.
        exists Hvm2_spawn_w.
        exact Hvm2_w.
        f_equal. apply ProofIrrelevance.proof_irrelevance. }
      assert (Hpre :
        @morphism _ _ _ _
          (compose (terminate_vm pid1)
                   (spawn_vm child_mb_t child_cont pid2 mb_t2 parent_cont))
          {| world := vm0_w; runq := []; ref_ctr := vm2_rc;
             inv_valid_pids := Forall_nil (proc_valid_pid vm2_rc) |}
          {| world := Hvm2_spawn_w;
             runq :=
               {| pid := pid2; proc_mb_t := mb_t2;
                  cont := parent_cont {| mba_pid := new_pid |} |}
               :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                  :: [];
             ref_ctr := new_pid_rc;
             inv_valid_pids :=
               Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}).
      { exists {| world := vm2_w; runq := []; ref_ctr := vm2_rc;
                 inv_valid_pids := Forall_nil (proc_valid_pid vm2_rc) |}.
        split > [exact Hleg1 | exact Hleg2]. }
      destruct (proj1 (h_spawn_terminate_commutativity child_mb_t child_cont mb_t2 parent_cont
                                            true pid1 pid2 Hpid12 _ _) Hpre)
        as [vm_c' [[vm_m [HsS HsT]] Heq_vm_c']].
      destruct vm_c' as [w_fin rq_fin rc_fin inv_fin].
      (* the swapped run spawns first, at the initial counter *)
      unfold spawn_vm, totalize in HsS. cbn in HsS.
      destruct HsS as [_v2s HsS].
      unfold spawn in HsS. cbn in HsS.
      unfold do_spawn in HsS. cbn in HsS.
      rewrite (Fresh.make_valid_eq pid2 vm2_rc new_pid new_pid_rc Hmake_pid) in HsS. cbn in HsS.
      destruct HsS as [w_mid Hw_mid1 Hvm_m_eq].
      subst vm_m.
      (* and terminates second, at the post-spawn counter *)
      unfold terminate_vm, totalize in HsT. cbn in HsT.
      destruct HsT as [_v1s HsT].
      unfold terminate in HsT. cbn in HsT.
      unfold do_exit in HsT. cbn in HsT.
      destruct HsT as [Hterm_mid [Hrq_eq Hrc_eq]].
      subst rq_fin. subst rc_fin.
      cbn in Heq_vm_c'.
      destruct Heq_vm_c' as [Hw_fin [Hrc_fin Hrq_fin]].
      (* Invariants *)
      assert (INV_RQ2' : Forall (proc_valid_pid vm2_rc) rq2').
      { eapply pick_forall_rest > [exact vm0_pids_valid | exact Hpick_proc2]. }
      assert (INV_MID : Forall (proc_valid_pid new_pid_rc)
        ({| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
         :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq2')).
      { constructor >
          [ (eapply Fresh.make_keeps_valid > [exact Hpid2_valid | exact Hmake_pid])
          | (constructor >
              [ exact (Fresh.makes_valid_ref pid2 new_pid vm2_rc new_pid_rc Hmake_pid)
              | (eapply make_keeps_valid_Forall > [exact INV_RQ2' | exact Hmake_pid]) ]) ]. }
      assert (INV_RQ3' : Forall (proc_valid_pid vm2_rc) rq3').
      { eapply pick_forall_rest > [exact INV_RQ2' | exact Hpick_proc1]. }
      assert (INV_FIN : Forall (proc_valid_pid new_pid_rc)
        ({| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
         :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq3')).
      { constructor >
          [ (eapply Fresh.make_keeps_valid > [exact Hpid2_valid | exact Hmake_pid])
          | (constructor >
              [ exact (Fresh.makes_valid_ref pid2 new_pid vm2_rc new_pid_rc Hmake_pid)
              | (eapply make_keeps_valid_Forall > [exact INV_RQ3' | exact Hmake_pid]) ]) ]. }
      assert (Hpick_proc1' :
        Pick ({| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
              :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq2')
             {| pid := pid1; proc_mb_t := mb_t1; cont := exit mb_t1 |}
             ({| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
              :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq3')).
      { apply pick_cons_rev. apply pick_cons_rev. exact Hpick_proc1. }
      (* Build the swapped run: spawn first, then exit *)
      exists {| world := w_fin;
               runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
                        :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq3';
               ref_ctr := new_pid_rc;
               inv_valid_pids := INV_FIN |}.
      split.
      + exists {| world := w_mid;
                  runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
                           :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq2';
                  ref_ctr := new_pid_rc;
                  inv_valid_pids := INV_MID |}.
        split.
        * (* spawn *)
          simpl.
          vm_step_some {| world := vm0_w; runq := rq2'; ref_ctr := vm2_rc;
                          inv_valid_pids := INV_RQ2' |}.
          sauto.
          unfold exec_proc_morph. cbn. unfold do_spawn. cbn. solve_alloc_pid. cbn.
          exists w_mid.
          exact Hw_mid1.
          f_equal. apply ProofIrrelevance.proof_irrelevance.
        * (* exit *)
          simpl.
          vm_step_some {| world := w_mid;
                          runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
                                   :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq3';
                          ref_ctr := new_pid_rc;
                          inv_valid_pids := INV_FIN |}.
          unfold schedule_out. cbn. split > [exact Hpick_proc1' | split > [reflexivity | reflexivity]].
          unfold exec_proc_morph. cbn.
          split > [ eapply h_terminate_morph_pi; eassumption
                  | split > [reflexivity | reflexivity] ].
      + split > [exact Hw_fin |
                 split > [reflexivity
                         | (repeat (apply perm_skip); apply Permutation_sym; exact Hrq3'equiv) ]].
    - (* spawn -> exit *)
      unfold_vm_step_morph Hvm1.
      simpl in Hvm2.
      unfold_vm_step_morph Hvm2.
      injection Hvm1_eq_vm as E1 E2 E3.
      subst vm2_w vm2_rq vm2_rc.
      clear Hvm1_eq_vm E1 E2 E3.
      unfold_schedule_out Hvm0_out.
      unfold_schedule_out HHvm2_out.
      cbn in Hpid1_valid, Hpid2_valid.
      subst vm0_out_w.
      subst Hvm2_out_w.
      subst vm0_out_rc.
      subst Hvm2_out_rc.
      subst.
      (* The process scheduled out second (exit) cannot be among the
         processes added to the queue by the first spawn (their pids differ): *)
      assert (Hne_parent :
        {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
        <> {| pid := pid1; proc_mb_t := mb_t1; cont := exit mb_t1 |}).
      { intros Heq. injection Heq as Hpid_eq Hmb Hcnt.
        apply not_eq_sym in Hpid12. now apply Hpid12. }
      destruct (pick_cons HHvm2_out_pick Hne_parent) as [rq_a [Heq_a Hpick_a]].
      subst vm4_rq.
      assert (Hne_child :
        {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
        <> {| pid := pid1; proc_mb_t := mb_t1; cont := exit mb_t1 |}).
      { intros Heq. injection Heq as Hpid_eq Hmb Hcnt.
        exact (Fresh.make_valid_not_equal pid2 pid1 new_pid vm0_rc vm4_rc
                 Hpid1_valid Hmake_pid Hpid_eq). }
      destruct (pick_cons Hpick_a Hne_child) as [rq_b [Heq_b Hpick_b]].
      subst rq_a.
      (* Run queue *)
      destruct (pick_two Hvm0_out_pick Hpick_b)
        as [rq2' [rq3' [Hpick_proc1 [Hpick_proc2 Hrq3'equiv]]]].
      assert (Hne : pid1 <> new_pid).
      { apply not_eq_sym.
        exact (Fresh.make_valid_not_equal pid2 pid1 new_pid vm0_rc vm4_rc
                 Hpid1_valid Hmake_pid). }
      ltac1:(pose proof vm2_pids_valid as HI2).
      ltac1:(inversion HI2 as [|? ? HI_p2s HI2r]).
      ltac1:(inversion HI2r as [|? ? HI_c2s _]).
      assert (Hv1 : is_valid_pid pid1 vm4_rc).
      { ltac1:(eapply Fresh.make_keeps_valid; [exact Hpid1_valid | exact Hmake_pid]). }
      assert (HlegS :
        @morphism _ _ _ _
          (spawn_vm child_mb_t child_cont pid2 mb_t2 parent_cont)
          {| world := vm0_w; runq := []; ref_ctr := vm0_rc;
             inv_valid_pids := Forall_nil (proc_valid_pid vm0_rc) |}
          {| world := Hvm1_spawn_w;
             runq :=
               {| pid := pid2; proc_mb_t := mb_t2;
                  cont := parent_cont {| mba_pid := new_pid |} |}
               :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                  :: [];
             ref_ctr := vm4_rc;
             inv_valid_pids :=
               Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}).
      { unfold spawn_vm, totalize. cbn.
        exists Hpid2_valid.
        unfold spawn. cbn. unfold do_spawn. cbn.
        rewrite (Fresh.make_valid_eq pid2 vm0_rc new_pid vm4_rc Hmake_pid). cbn.
        exists Hvm1_spawn_w.
        exact Hvm1_w.
        f_equal. apply ProofIrrelevance.proof_irrelevance. }
      assert (HlegT :
        @morphism _ _ _ _ (terminate_vm pid1)
          {| world := Hvm1_spawn_w;
             runq :=
               {| pid := pid2; proc_mb_t := mb_t2;
                  cont := parent_cont {| mba_pid := new_pid |} |}
               :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                  :: [];
             ref_ctr := vm4_rc;
             inv_valid_pids :=
               Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}
          {| world := vm4_w;
             runq :=
               {| pid := pid2; proc_mb_t := mb_t2;
                  cont := parent_cont {| mba_pid := new_pid |} |}
               :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                  :: [];
             ref_ctr := vm4_rc;
             inv_valid_pids :=
               Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}).
      { unfold terminate_vm, totalize. cbn.
        exists Hv1.
        unfold terminate. cbn. unfold do_exit. cbn.
        split.
        - ltac1:(eapply h_terminate_morph_pi; eassumption).
        - split > [reflexivity | reflexivity]. }
      assert (Hpre :
        @morphism _ _ _ _
          (compose (spawn_vm child_mb_t child_cont pid2 mb_t2 parent_cont)
                   (terminate_vm pid1))
          {| world := vm0_w; runq := []; ref_ctr := vm0_rc;
             inv_valid_pids := Forall_nil (proc_valid_pid vm0_rc) |}
          {| world := vm4_w;
             runq :=
               {| pid := pid2; proc_mb_t := mb_t2;
                  cont := parent_cont {| mba_pid := new_pid |} |}
               :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                  :: [];
             ref_ctr := vm4_rc;
             inv_valid_pids :=
               Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}).
      { exists {| world := Hvm1_spawn_w;
                 runq :=
                   {| pid := pid2; proc_mb_t := mb_t2;
                      cont := parent_cont {| mba_pid := new_pid |} |}
                   :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |}
                      :: [];
                 ref_ctr := vm4_rc;
                 inv_valid_pids :=
                   Forall_cons _ HI_p2s (Forall_cons _ HI_c2s (Forall_nil _)) |}.
        split > [exact HlegS | exact HlegT]. }
      destruct (proj2 (h_spawn_terminate_commutativity child_mb_t child_cont mb_t2 parent_cont
                                               true pid1 pid2 Hpid12 _ _) Hpre)
        as [vm_c' [[vm_m [HsT HsS]] Heq_vm_c']].
      destruct vm_m as [w_mid rq_mid rc_mid inv_mid].
      (* the swapped run terminates first, from the initial counter *)
      unfold terminate_vm, totalize in HsT. cbn in HsT.
      destruct HsT as [_v1s HsT].
      unfold terminate in HsT. cbn in HsT.
      unfold do_exit in HsT. cbn in HsT.
      destruct HsT as [Hterm_mid [Hrq_mid Hrc_mid]].
      subst rq_mid. subst rc_mid.
      (* then spawns, also from the initial counter *)
      unfold spawn_vm, totalize in HsS. cbn in HsS.
      destruct HsS as [_v2s HsS].
      unfold spawn in HsS. cbn in HsS.
      unfold do_spawn in HsS. cbn in HsS.
      rewrite (Fresh.make_valid_eq pid2 vm0_rc new_pid vm4_rc Hmake_pid) in HsS. cbn in HsS.
      destruct HsS as [w_fin Hspawn_mid Hvm_c'_eq].
      subst vm_c'.
      cbn in Heq_vm_c'.
      destruct Heq_vm_c' as [Hw_fin [Hrc_fin Hrq_fin]].
      (* Invariants *)
      assert (INV_RQ2' : Forall (proc_valid_pid vm0_rc) rq2').
      { eapply pick_forall_rest > [exact vm0_pids_valid | exact Hpick_proc1]. }
      assert (INV_RQ3' : Forall (proc_valid_pid vm0_rc) rq3').
      { eapply pick_forall_rest > [exact INV_RQ2' | exact Hpick_proc2]. }
      assert (INV_FIN : Forall (proc_valid_pid vm4_rc)
        ({| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
         :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq3')).
      { constructor >
          [ (eapply Fresh.make_keeps_valid > [exact Hpid2_valid | exact Hmake_pid])
          | (constructor >
              [ exact (Fresh.makes_valid_ref pid2 new_pid vm0_rc vm4_rc Hmake_pid)
              | (eapply make_keeps_valid_Forall > [exact INV_RQ3' | exact Hmake_pid]) ]) ]. }
      (* Build the swapped run: exit first, then spawn *)
      exists {| world := w_fin;
               runq := {| pid := pid2; proc_mb_t := mb_t2; cont := parent_cont {| mba_pid := new_pid |} |}
                        :: {| pid := new_pid; proc_mb_t := child_mb_t; cont := child_cont |} :: rq3';
               ref_ctr := vm4_rc;
               inv_valid_pids := INV_FIN |}.
      split.
      + exists {| world := w_mid; runq := rq2'; ref_ctr := vm0_rc;
                  inv_valid_pids := INV_RQ2' |}.
        split.
        * (* exit *)
          simpl.
          vm_step_some {| world := vm0_w; runq := rq2'; ref_ctr := vm0_rc;
                          inv_valid_pids := INV_RQ2' |}.
          destruct vm0_rq as [|y ys] >
            [ ltac1:(exfalso; inversion Hpick_proc1)
            | unfold schedule_out; cbn;
              split > [exact Hpick_proc1 | split > [reflexivity | reflexivity]] ].
          unfold exec_proc_morph. cbn.
          split > [ eapply h_terminate_morph_pi; eassumption
                  | split > [reflexivity | reflexivity] ].
        * (* spawn *)
          simpl.
          vm_step_some {| world := w_mid; runq := rq3'; ref_ctr := vm0_rc;
                          inv_valid_pids := INV_RQ3' |}.
          destruct rq2' as [|y ys] >
            [ ltac1:(exfalso; inversion Hpick_proc2)
            | unfold schedule_out; cbn;
              split > [exact Hpick_proc2 | split > [reflexivity | reflexivity]] ].
          unfold exec_proc_morph. cbn. unfold do_spawn. cbn. solve_alloc_pid. cbn.
          exists w_fin.
          exact Hspawn_mid.
          f_equal. apply ProofIrrelevance.proof_irrelevance.
      + split > [exact Hw_fin |
                 split > [reflexivity
                         | (repeat (apply perm_skip); apply Permutation_sym; exact Hrq3'equiv) ]].
  Qed.
End commute.
