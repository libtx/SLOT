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

Section VM.
  Context `{IOH : IOHandler}.

  Let World := @h_state _ _ IOH.

  Let Heqiv_w := @h_setoid _ _ IOH.

  (** ** Processes
   *** Programs
   [Program] datatype defines all primitives used by the business logic.
   *)
  CoInductive Program (Mailbox : Set) : Type :=
  (** Program termintes: *)
  | die :
    Program Mailbox
  (** Interrupt the computation without producing any side effects.

      This primitive is used to softly introduce the concept of
      Erlang's "reductions", and to side-step termination checker,
      making programs non-Turing in a practically useful, as opposed
      to forced, way.

      In Erlang, reduction counting improves responsiveness of the
      system, in SLOT it *additionally* gives a structural argument
      "for free". *)
  | p_yield :
    forall (continuation : Program Mailbox),
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
      Program Mailbox.

  (** *** Process
      [Process] is defined via its pid,
      type of messages it can receive in the main mailbox ([proc_mb_t]),
      and continuation, which is [Program]. *)
  Record Process :=
    mkProcess
      { pid : Ref;
        proc_mb_t : Set;
        cont : @Program proc_mb_t;
      }.

  Inductive Event :=
  | e_p : Process -> Event.

  (* begin hide *)
  #[export] Instance etaProc : Settable _ := settable! mkProcess <pid; proc_mb_t; cont>.
  (* end hide *)

  Definition proc_valid_pid ref_ctr proc := Fresh.is_valid_ref (pid proc) ref_ctr = true.

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
        (** Invariant: all processes have valid pids: *)
        inv_valid_pids : Forall (proc_valid_pid ref_ctr) runq;
      }.

  Definition vm_eq (a b : VM) : Prop :=
    world a = world b /\ runq a = runq b /\ ref_ctr a = ref_ctr b.

  (* begin hide *)
  #[export] Instance etaVM : Settable _ := settable! mkVM <world; runq; ref_ctr; inv_valid_pids>.
  (* end hide *)

  Global Program Instance vm_setoid : Setoid VM :=
    {| equiv a b :=
        match a, b with
          {| world := w1; runq := rq1; ref_ctr := rc1 |},
          {| world := w2; runq := rq2; ref_ctr := rc2 |} =>
            w1 =h= w2 /\ rc1 =s= rc2 /\ rq1 =p= rq2
        end
    |}.
  Next Obligation with sauto use:Permutation_sym,Permutation_trans.
    split; unfold Reflexive,Symmetric,Transitive.
    - intros a. destruct a...
    - intros a b. destruct a, b...
    - intros a b c. destruct a, b, c. repeat split...
  Qed.

  (** ** Canonical order *)

  Definition vmte_canon_rel (a b : Process) :=
    (* Order of events is canonical when pid a =< pid b: *)
    match RefOrd.compare_ (pid a) (pid b) with
    | Gt => False
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
    sauto use:RefOrd.compare_asymm.
  Qed.

  Global Instance vmevCanonOrder : CanonicalOrder vmte_canon_rel :=
    { canon_rel_dec := vmte_canon_rel_dec;
      canon_rel_total := vmte_canon_rel_total;
    }.

  Lemma make_keeps_valid_Forall (parent new : Ref) (cc cc' : Fresh.t) l :
    Forall (fun x => Fresh.is_valid_ref (pid x) cc = true) l ->
    Fresh.make parent cc = (new, cc') ->
    Forall (fun x => Fresh.is_valid_ref (pid x) cc' = true) l.
  Proof.
    induction l as [|a l]; intros Hl Hcc'.
    - constructor.
    - inversion Hl; subst.
      constructor.
      + eapply Fresh.make_keeps_valid; eauto.
      + apply IHl; easy.
  Qed.

  Lemma Forall_is_valid_pid_equiv rc rc' rq :
    rc == rc' ->
    Forall (proc_valid_pid rc) rq ->
    Forall (proc_valid_pid rc') rq.
  Proof.
    generalize dependent rc.
    generalize dependent rc'.
    induction rq.
    - constructor.
    - intros rc rc' H H1.
      inversion_clear H1.
      constructor.
      + apply Fresh.is_valid_equiv with (cc := rc'); assumption.
      + apply IHrq with (rc := rc'); assumption.
  Qed.
  (** ** Schedule out *)

  Definition MaybeValidProc : Type := option (Process * VM).

  Program Definition schedule_out : MFun VM MaybeValidProc :=
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
                        (* TODO: invariants *)
                  end
              end
          end
      |}.
  Next Obligation with try easy.
    destruct x as [w rq rc inv].
    destruct x' as [w' rq' rc' inv'].
    destruct rq as [|rq_ rq_rest]; simpl in *;
      destruct H as [Hw [Hrc Hperm]].
    - exists None. split.
      + destruct rq' as [|rq'_ rq'_rest]...
        now apply Permutation_nil in Hperm.
      + now subst.
    - destruct y as [[proc vm2]|]...
      destruct vm2 as [w2 rq2 rc2 inv2].
      destruct H0 as [Hpick_proc [Hw2 Hrc2]].
      subst.
      apply pick_equiv with (l1' := rq') in Hpick_proc...
      destruct Hpick_proc as [rq2' [Hpick_proc' Hrq2']].
      assert (inv'' : Forall (proc_valid_pid rc') rq2'). {
        rewrite <-Hrq2'.
        apply Forall_is_valid_pid_equiv with (rc := rc2)...
      }
      exists (Some (proc, {|world := w'; runq := rq2'; ref_ctr := rc'; inv_valid_pids := inv'' |})).
      simpl. split; [|split]...
      destruct rq' as [|rq'_ rq'_rest].
      + exfalso.
        now apply Permutation_sym, Permutation_nil in Hperm.
      + repeat split...
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

  Lemma schedule_out_valid_pid_prev vm proc vm' :
    vm ~[schedule_out]~> Some (proc, vm') ->
    proc_valid_pid (ref_ctr vm) proc.
  Proof.
    unfold proc_valid_pid, schedule_out. simpl.
    intros Hsched.
    destruct vm as [w rq rc Hinv].
    destruct vm' as [w' rq' rc' Hinv'].
    destruct rq as [|_first _rest].
    - discriminate.
    - destruct Hsched as [Hpick [Hworld Hrc]].
      simpl.
      now apply pick_forall_elem with (a := proc) (l' := rq') in Hinv.
  Qed.

  Lemma schedule_out_valid_pid vm proc vm' :
    vm ~[schedule_out]~> Some (proc, vm') ->
    proc_valid_pid (ref_ctr vm') proc.
  Proof.
    intros H.
    destruct vm as [w rq rc inv].
    simpl in H.
    destruct rq as [|_first _rest].
    - discriminate.
    - destruct vm' as [w' rq' rc' inv'].
      destruct H as [Hrq' [Hw' Hrc']]. subst. simpl.
      now apply pick_forall_elem with (a := proc) (l' := rq') (l := _first :: _rest).
  Qed.

  (** ** Operations with the world *)

  Program Definition lift_w_ret {Ret : Type} `{Heqiv_r : Setoid Ret}
    (w_morph : @MFunRet Ret World Heqiv_r Heqiv_w) : @MFunRet Ret VM Heqiv_r vm_setoid :=
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
    exists (ret', {| world := w2'; runq := rq1'; ref_ctr := rc1'; inv_valid_pids := inv_valid_pids1 |}).
    repeat split; try assumption.
    - apply Hrc.
  Qed.

  Program Definition lift_w (w_morph : @MFun World World Heqiv_w Heqiv_w) : @MFun VM VM vm_setoid vm_setoid :=
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
    exists {| world := w2'; runq := rq1'; ref_ctr := rc1'; inv_valid_pids := inv_valid_pids1 |}.
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
      exists {| world := w3'; ref_ctr := rc3; runq := rq3; inv_valid_pids := inv_valid_pids2 |}.
    - split; [exists {| world := w2'; ref_ctr := rc3; runq := rq3; inv_valid_pids := inv_valid_pids2 |} |]; sauto.
    - split; [exists {| world := w2'; ref_ctr := rc3; runq := rq3; inv_valid_pids := inv_valid_pids2 |} |]; sauto.
  Qed.

  (** ** Spawn *)

  (* begin details *)
  Lemma schedule_in_new_inv
    (parent : Ref)
    (rq : list Process)
    (rc : Fresh.t)
    (inv_valid : Forall (proc_valid_pid rc) rq)
    (new : Ref)
    (rc' : Fresh.t)
    (Heqfresh : Fresh.make parent rc = (new, rc'))
    (Hnewvalid : Fresh.is_valid_ref new rc' = true) :
    Forall (proc_valid_pid rc') rq.
  Proof.
    induction inv_valid as [|proc l Hproc Hl IH].
    - constructor.
    - constructor.
      + apply Fresh.make_keeps_valid with (new := new) (cc := rc) (parent := parent); assumption.
      + assumption.
  Qed.
  (* end details *)

  Section spawn.
    Context
      (child_mb_t : Set) (child_cont : Program child_mb_t)
      (parent : Ref) (parent_mb_t : Set)
      (parent_cont : @Address child_mb_t -> Program parent_mb_t).

    Lemma do_spawn_keeps_invariniant
      addr
      (rq : list Process)
      (rc rc' : Fresh.t)
      (new : Ref)
      (inv_valid : Forall (proc_valid_pid rc) rq)
      (parent_valid : Fresh.is_valid_ref parent rc = true)
      (Hnewvalid : Fresh.is_valid_ref new rc' = true)
      (Heqfresh : Fresh.make parent rc = (new, rc'))
      (inv_valid' : Forall (proc_valid_pid rc') rq) :
      Forall (proc_valid_pid rc')
        ({| pid := parent; proc_mb_t := parent_mb_t; cont := parent_cont addr |}
           :: {| pid := new; proc_mb_t := child_mb_t; cont := child_cont |} :: rq).
    Proof.
      apply Forall_cons_iff. split.
      - eapply Fresh.make_keeps_valid; eauto.
      - eapply Forall_cons_iff. split; assumption.
    Qed.

    (** Allocate a new pid for a process and add it to the VM.
        Update the parent process (which should be scheduled out),
        and add it to the VM too *)
    Definition do_spawn
      (vm : VM)
      (parent_valid : Fresh.is_valid_ref parent (ref_ctr vm) = true) : VM.
    Proof.
      destruct vm as [w rq rc inv_valid].
      destruct (Fresh.make_valid parent rc) as [new rc' Hnewvalid Heqfresh].
      specialize (schedule_in_new_inv parent rq rc inv_valid new rc' Heqfresh Hnewvalid) as inv_valid'.
      set (addr := mkAddress child_mb_t new).
      set (rq' :=
             {| pid := parent; proc_mb_t := parent_mb_t; cont := parent_cont addr |} ::
             {| pid := new; proc_mb_t := child_mb_t; cont := child_cont |} ::
             rq).
      assert (inv_valid'' : Forall (proc_valid_pid rc') rq'). {
        apply (do_spawn_keeps_invariniant addr rq rc rc' new inv_valid parent_valid Hnewvalid Heqfresh inv_valid').
      }
      exact {| world := h_spawn new child_mb_t w; runq := rq'; ref_ctr := rc'; inv_valid_pids := inv_valid''|}.
    Defined.

    Lemma do_spawn_covariance
      (vm vm' : VM)
      (Hvm' : vm == vm')
      (parent_valid : Fresh.is_valid_ref parent (ref_ctr vm) = true)
      (parent_valid' : Fresh.is_valid_ref parent (ref_ctr vm') = true) :
      do_spawn vm parent_valid == do_spawn vm' parent_valid'.
    Proof.
      destruct vm as [w1 rq1 rc1 inv1].
      destruct vm' as [w1' rq1' rc1' inv1'].
      unfold do_spawn.
      destruct (Fresh.make_valid parent rc1) as [new_pid rc2 H_1 H_2].
      destruct (Fresh.make_valid parent rc1') as [new_pid' rc2' H_1' H_2'].
      simpl.
      simpl in Hvm'. destruct Hvm' as [Hw [Hrc Hrq]].
      specialize (Fresh.make_morph parent rc1 rc1' Hrc) as H.
      rewrite H_2, H_2' in H.
      simpl in H. destruct H as [Hpids Hrc2]. subst.
      split; [|split].
      - now apply h_spawn_covariance.
      - assumption.
      - now repeat apply perm_skip.
    Qed.
  End spawn.

  Definition exec_proc_morph (vm0 vm1 vm2 : VM) (proc : Process) (Hproc : vm0 ~[schedule_out]~> Some (proc, vm1)) : Prop.
  Proof.
    set (proc_ := proc).
    destruct (cont proc) as [|cont|req cont|child_mb_t child child_cont].
    - (* die *)
      exact (vm1 ~[lift_w (h_terminate (pid proc))]~> vm2).
    - (* yield; TODO *)
      exact False.
    - (* io: TODO *)
      exact False.
    - (* spawn *)
      refine (vm_eq vm2 (do_spawn child_mb_t child (pid proc) (proc_mb_t proc) child_cont vm1 _)).
      specialize (schedule_out_valid_pid vm0 proc vm1) as H.
      now apply H in Hproc.
  Defined.

  Inductive vm_step_morph : VM -> option (Process * VM) -> Prop :=
  | vm_step_nil : forall vm,
      vm ~[schedule_out]~> None ->
      vm_step_morph vm None
  | vm_step_some : forall vm0 vm1 vm2 proc (Hproc : vm0 ~[schedule_out]~> Some (proc, vm1)),
      exec_proc_morph vm0 vm1 vm2 proc Hproc ->
      vm_step_morph vm0 (Some (proc, vm2)).

  Program Definition vm_step : @MFun VM (@ts_ret VM Process) vm_setoid (ts_ret_setoid Process vm_setoid) :=
    {| morphism := vm_step_morph;
       morphism_covariance vm0 vm0' ret Hequiv Hret := _;
    |}.
  Next Obligation.
    inversion Hret as [|H vm1 vm2 proc Hvm1 Hvm2]; subst; clear Hret.
    - destruct vm0 as [w0 rq0 rc0 inv0].
      destruct vm0' as [w0' rq0' rc0' inv0'].
      destruct Hequiv as [Hw [Hrc Hrq]].
      exists None. split; [|easy].
      simpl in H.
      destruct rq0.
      + apply Permutation_nil in Hrq. subst.
        now constructor.
      + contradiction.
    - destruct (morphism_covariance schedule_out vm0 vm0' (Some (proc, vm1)) Hequiv Hvm1) as [ret1' Hret1'].
      destruct ret1' as [[proc' vm1']|]; [| exfalso; sauto].
      destruct Hret1' as [Hvm1' Hequiv1].
      unfold equiv, setoid_option, equiv, pair_setoid in Hequiv1.
      destruct Hequiv1 as [Hproc'proc Hvm1'vm1].
      simpl in Hproc'proc. rewrite <-Hproc'proc in *. clear Hproc'proc proc'.

      unfold exec_proc_morph in Hvm2.
      remember (cont proc) as cont_.
      destruct cont_ as [| | |child_mb_t child_cont cont].
      + (* die *)
        morph_shift (lift_w (h_terminate (pid proc))) vm1'.
        exists (Some (proc, vm2')).
        split.
        *  constructor 2 with (vm1 := vm1') (Hproc := Hvm1').
           unfold exec_proc_morph. rewrite <-Heqcont_.
           assumption.
        * sauto.
      + (* yield: TODO *) contradiction.
      + (* io: TODO *) contradiction.
      + (* spawn *)
        subst.
        specialize (do_spawn_covariance child_mb_t child_cont (pid proc) (proc_mb_t proc) cont vm1 vm1' Hvm1'vm1
                      (schedule_out_valid_pid vm0 proc vm1 Hvm1)
                      (schedule_out_valid_pid vm0' proc vm1' Hvm1')) as H.
        exists (Some (proc, (do_spawn child_mb_t child_cont (pid proc) (proc_mb_t proc) cont vm1' (schedule_out_valid_pid vm0' proc vm1' Hvm1')))).
        split.
        * constructor 2 with (vm1 := vm1') (Hproc := Hvm1').
          unfold exec_proc_morph. rewrite <-Heqcont_.
          sauto.
        * sauto.
  Qed.

  Global Instance vmTransitionSystem : @TransitionSystem VM Process :=
    {|
      ts_setoid := vm_setoid;
      ts_canon_rel := vmte_canon_rel;
      ts_canon_order := vmevCanonOrder;
      ts_state_trans := vm_step
    |}.
End VM.

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
       let inv := fresh_id (String.app prefix "_pids_valid") in
       let vm_ := Control.hyp vm in
       destruct $vm_ as [$w $rq $rc $inv])
    vms.

Ltac2 Notation "dvm" ids(list0(ident)) := dvm ids.

Section tests.
  Context `{IO: IOHandler}.

  Goal forall (vm1 vm2 : VM), vm1 = vm2 -> False.
    intros vm1 vm2 H.
    dvm vm1 vm2.
  Abort.
End tests.

Section canned.
  Context `{IOH : IOHandler}.

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
    ltac1:(sauto).
  Qed.
End canned.

Ltac2 maybe_hyp_to_string (c : constr) (default : string) : string :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var c => Ident.to_string c
  | _ => default
  end.

Ltac2 unfold_vm_step_morph (id : ident) :=
  lazy_match! Constr.type (Control.hyp id) with
  | vm_step_morph ?vm_start (Some (?proc, ?vm_end)) =>
      let prefix := maybe_hyp_to_string vm_start "" in
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
      unfold exec_proc_morph, vm_eq in $id; simpl in $id
  end.

Ltac2 Notation "unfold_vm_step_morph" x(ident) := unfold_vm_step_morph x.

(* Use equations instead? *)
Ltac2 unfold_alloc_pid (pid : constr) (rc : constr) new_ident :=
  let prefix := Ident.to_string new_ident in
  let new_pid := fresh_id prefix in
  let new_rc := fresh_id (String.app prefix "_rc") in
  let valid := fresh_id (String.app "H" (String.app prefix "_valid")) in
  let inv := fresh_id (String.app "H" (String.app (String.app prefix "_rc") "_valid")) in
  let h_alloc_old := fresh_id (String.app "H_alloc_" (Ident.to_string new_pid)) in
  destruct (Fresh.make_valid $pid $rc) as [$new_pid $new_rc $valid $inv].

Ltac2 Notation "unfold_alloc_pid" pid(constr) rc(constr) new(seq("as", ident)) := unfold_alloc_pid pid rc new.

Notation "'P<' T > A @ C " := {| pid := A; proc_mb_t := T; cont := C |} (at level 100).

Section commute.
  Context `{IOH : IOHandler}.

  Let req_t := h_request_t IOH.
  Let rep_t := h_reply_t IOH.
  Let prog_t := @Program req_t rep_t.

  Ltac2 simpl_fresh_ref () :=
    unfold proc_valid_pid;
    match! goal with
    | [ hnew : Fresh.make ?parent ?rc0 = (?new, ?rc) |- Fresh.is_valid_ref ?new ?rc = true ] =>
        let h := Control.hyp hnew in
        apply (Fresh.makes_valid_ref $parent $new $rc0 $rc $h)
    | [ h : Fresh.make ?parent ?rc0 = (?new, ?rc) |- Fresh.is_valid_ref ?pid ?rc = true ] =>
        apply Fresh.make_keeps_valid with (new := $new) (parent := $parent) (cc := $rc0) > [|assumption]
    end.

  (* Solve goal of type
     [Forall (fun proc : Process => Fresh.is_valid_ref (pid proc) rc = true) rq] *)
  Ltac2 Notation "simpl_fresh_ref" := simpl_fresh_ref ().

  Ltac2 solve_fresh_ref () :=
    constructor > [now repeat (simpl_fresh_ref)|].

  Ltac2 Notation "solve_fresh_ref" := solve_fresh_ref ().

  Ltac2 solve_alloc_pid () :=
    simpl;
    lazy_match! goal with
      [ h_new : Fresh.make ?pid ?rc0 = (?new, ?rc1) |- context [Fresh.make_valid ?pid ?rc0] ] =>
        let h := Control.hyp h_new in
        rewrite (Fresh.make_valid_eq $pid $rc0 $new $rc1 $h)
    end.

  Ltac2 Notation "solve_alloc_pid" := solve_alloc_pid ().

  (* Simplify all available hypotheses of type Forall (.. is_valid_ref.. ) (a :: b :: ..) *)
  Ltac2 unfold_rc_invarinats () :=
    repeat (
        lazy_match! goal with
        | [ h : Forall (fun x : Process => Fresh.is_valid_ref (pid x) _ = true) (?a :: ?l)  |- _
          ] =>
            let h := Control.hyp h in
            let ha := fresh_id (String.app "H_valid_" (maybe_hyp_to_string a "a")) in
            let hl := fresh_id (String.app "H_valid_" (maybe_hyp_to_string l "l")) in
            let hx := Fresh.in_goal @h in
            inversion_clear $h as [|? ? $ha $hl $hx];
            simpl in $ha;
            simpl in $hl
        end).

  Ltac2 rec solve_rc_invariant2 () :=
    match! goal with
    | [ |- Forall _ [] ] =>
        now constructor
    | [ |- Fresh.is_valid_ref _ _ = true ] =>
        repeat (simpl_fresh_ref); assumption
    | [ |- Forall (fun x => Fresh.is_valid_ref (pid x) _ = true) (_ ++ _) ] =>
        apply Forall_app; split; Control.enter solve_rc_invariant2
    | [ |- Forall (fun x => Fresh.is_valid_ref (pid x) _ = true) (_ :: _) ] =>
        apply Forall_cons; Control.enter solve_rc_invariant2
    | [ hmake : Fresh.make ?parent ?rc1 = (?new, ?rc2)
        |- Forall (fun x => Fresh.is_valid_ref (pid x) ?rc2 = true) ?l
      ] =>
        let hmake := Control.hyp hmake in
        refine '(make_keeps_valid_Forall $parent $new $rc1 $rc2 $l _ $hmake);
        Control.enter solve_rc_invariant2
    | [ _ : Pick ?l ?elem ?l'
        |- Forall (fun x => Fresh.is_valid_ref (pid x) _ = true) ?l'
      ] =>
        apply pick_forall_rest with (l := $l) (l' := $l') (a := $elem);
        Control.enter solve_rc_invariant2
    | [ h : Pick ?l ?elem ?l'
        |- Forall (fun x => Fresh.is_valid_ref (pid x) _ = true) ?l
      ] =>
        apply pick_forall_rest with (l := $l) (l' := $l') (a := $elem) in $h;
        Control.enter solve_rc_invariant2
    | [ |- _ ] =>
        assumption
    end.

  Ltac2 solve_rc_invariant () :=
    unfold proc_valid_pid in *;
    unfold_rc_invarinats;
    solve_rc_invariant2 ().

  Ltac2 Notation "solve_rc_invariant" := solve_rc_invariant ().

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

  Ltac2 solve_vm_step () :=
    lazy_match! goal with
    | [ _ : Pick ?rq0 ?proc ?rq1 |-
          vm_step_morph {| world := ?w; runq := ?rq0; ref_ctr := ?rc |} (Some (?proc, _))] =>
        let hinv := fresh_id (String.app "HInv_" (maybe_hyp_to_string rc "rc")) in
        assert ($hinv : Forall (proc_valid_pid $rc) $rq1) >
          [try assumption |
            let hinv := Control.hyp hinv in
            printf "%t" hinv;
            vm_step_some {| world := $w;
                            runq := $rq1;
                            ref_ctr := $rc;
                            inv_valid_pids := $hinv
                         |} >
              [|unfold exec_proc_morph, vm_eq]
          ]
    end.

  Lemma spawn_spawn_commute {pid1 pid2 mb_t1 mb_t2 child_mb_t1 child_mb_t2 child1 child2 cont1 cont2} :
    pid1 <> pid2 ->
    ts_event_commute_ctx
      (fun vm => Fresh.is_valid_ref pid1 (ref_ctr vm) = true /\
              Fresh.is_valid_ref pid2 (ref_ctr vm) = true)
      {| pid := pid1; proc_mb_t := mb_t1; cont := @p_spawn req_t rep_t mb_t1 child_mb_t1 child1 cont1 |}
      {| pid := pid2; proc_mb_t := mb_t2; cont := @p_spawn req_t rep_t mb_t2 child_mb_t2 child2 cont2 |}.
  Proof.
    intros Hpids12.
    unfold ts_event_commute_ctx, commute_ctx, commute_def, exists_equiv.
    intros vm0 vm4 [Hvalid_pid1 Hvalid_pid2].
    split >
            [|apply neq_symm in Hpids12;
              Std.rename [(@pid1, @pid2); (@pid2, @pid1);
                          (@Hvalid_pid1, @Hvalid_pid2); (@Hvalid_pid2, @Hvalid_pid1);
                          (@child1, @child2); (@child2, @child1);
                          (@mb_t1, @mb_t2); (@mb_t2, @mb_t1);
                          (@cont1, @cont2); (@cont2, @cont1);
                          (@child_mb_t1, @child_mb_t2); (@child_mb_t2, @child_mb_t1)]
            ];
      intros [vm2 [Hvm2 Hvm4]].
    - simpl in Hvm2, Hvm4.
      unfold_vm_step_morph Hvm2.
      unfold_vm_step_morph Hvm4.
      dvm vm0 vm0_out vm2 vm2_out vm4.
      cbn in Hvm2. cbn in Hvm4.
      unfold_alloc_pid pid1 vm0_out_rc as new_pid1.
      unfold_alloc_pid pid2 vm2_out_rc as new_pid2.
      apply canned_schedule_out_some in Hvm0_out as Hvm0_out_.
      apply canned_schedule_out_some in Hvm2_out as Hvm2_out_.
      destruct Hvm0_out_ as [Hvm0_pick [Hvm0_world Hvm0_rc]].
      destruct Hvm2_out_ as [Hvm2_pick [Hvm2_world Hvm2_rc]].
      simpl in Hvm4, Hvm2_rc, Hvm2_world, Hvm2_pick, Hvm0_rc, Hvm0_world, Hvm0_pick.
      destruct Hvm2 as [Hvm2_w [Hvm2_rq Hvm2_rc_]].
      destruct Hvm4 as [Hvm4_w [Hvm4_rq Hvm4_rc_]].
      subst.
      (* Start rebuilding runq *)
      destruct (pick_cons Hvm2_pick) as [vm2_out_rq1 [H1 H2]]. {
        intros Habsurd. now inversion Habsurd.
      }
      subst.
      destruct (pick_cons H2) as [vm2_out_rq2 [H1 H3]]. {
        specialize (Fresh.make_valid_not_equal pid1 pid2 new_pid1 vm0_out_rc new_pid1_rc Hvalid_pid2 Hnew_pid1_rc_valid) as H.
        intros Habsurd. now inversion Habsurd.
      }
      subst.
      destruct (pick_two Hvm0_pick H3) as [vm0_out' [vm2_out_rq2' [Hvm2_out' [Hpick_0' Hvm2_out_rq2'_equiv]]]].
      apply pick_app_rev with (new := [{| pid := pid2; proc_mb_t := mb_t2; cont := cont2 {| mba_pid := new_pid2 |} |};
                                       {| pid := new_pid2; proc_mb_t := child_mb_t2; cont := child2 |}]) in Hpick_0'.
      (* Run queue: *)
      set (rq' :=
             [{| pid := pid1; proc_mb_t := mb_t1; cont := cont1 {| mba_pid := new_pid1 |} |};
               {| pid := new_pid1; proc_mb_t := child_mb_t1; cont := child1 |};
               {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 {| mba_pid := new_pid2 |} |};
               {| pid := new_pid2; proc_mb_t := child_mb_t2; cont := child2 |}]
               ++ vm2_out_rq2').
      (* World: *)
      set (w' := h_spawn new_pid1 child_mb_t1 (h_spawn new_pid2 child_mb_t2 vm0_out_w)).
      (* Run queue invariant: *)
      destruct (Fresh.swap_make pid1 pid2 new_pid1 new_pid2 vm0_out_rc new_pid1_rc new_pid2_rc Hpids12 Hnew_pid1_rc_valid Hnew_pid2_rc_valid) as [rc2' [rc3' [Hrc' [Hnew_pid1' Hnew_pid2']]]].
      assert (Hvm_pids_valid : Forall (proc_valid_pid rc3') rq'). {
        subst rq'.
        rewrite Hvm2_out_rq2'_equiv.
        solve_rc_invariant.
      }
      (* Build it: *)
      exists {|
          world := w';
          runq := rq';
          ref_ctr := rc3';
          inv_valid_pids := Hvm_pids_valid;
        |}. split.
      2:{ split > [|split].
          - simpl. subst w'.
            apply h_spawn_commutativity.
            apply Fresh.new2_not_equal with (p1 := pid2) (p2 := pid1) (rc := vm0_out_rc) (rc' := rc2') (rc'' := rc3'); try assumption.
            symmetry. assumption.
          - now symmetry.
          - subst rq'.
            eapply Permutation_swap2; eauto.
            now symmetry.
      } {
        simpl.
        set (rq_ := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 {| mba_pid := new_pid2 |} |}
                      :: {| pid := new_pid2; proc_mb_t := child_mb_t2; cont := child2 |}
                      ::  vm0_out') in *.
        assert (Hinv_rc2'' :  Forall (proc_valid_pid vm0_out_rc) vm0_out') by solve_rc_invariant.
        assert (Hinv_rc2' : Forall (proc_valid_pid rc2') rq_). {
          subst rq_.
          solve_rc_invariant.
        }
        exists {|
            world := h_spawn new_pid2 child_mb_t2 vm0_out_w;
            runq := rq_;
            ref_ctr := rc2';
            inv_valid_pids := Hinv_rc2';
          |}.
        split.
        - solve_vm_step ().
          + sauto.
          + solve_alloc_pid. sauto.
        - solve_vm_step ().
          + solve_rc_invariant.
          + sauto.
          + solve_alloc_pid. sauto.
      }
    - (* The following is a carbon copy of the above *)
simpl in Hvm2, Hvm4.
      unfold_vm_step_morph Hvm2.
      unfold_vm_step_morph Hvm4.
      dvm vm0 vm0_out vm2 vm2_out vm4.
      cbn in Hvm2. cbn in Hvm4.
      unfold_alloc_pid pid1 vm0_out_rc as new_pid1.
      unfold_alloc_pid pid2 vm2_out_rc as new_pid2.
      apply canned_schedule_out_some in Hvm0_out as Hvm0_out_.
      apply canned_schedule_out_some in Hvm2_out as Hvm2_out_.
      destruct Hvm0_out_ as [Hvm0_pick [Hvm0_world Hvm0_rc]].
      destruct Hvm2_out_ as [Hvm2_pick [Hvm2_world Hvm2_rc]].
      simpl in Hvm4, Hvm2_rc, Hvm2_world, Hvm2_pick, Hvm0_rc, Hvm0_world, Hvm0_pick.
      destruct Hvm2 as [Hvm2_w [Hvm2_rq Hvm2_rc_]].
      destruct Hvm4 as [Hvm4_w [Hvm4_rq Hvm4_rc_]].
      subst.
      (* Start rebuilding runq *)
      destruct (pick_cons Hvm2_pick) as [vm2_out_rq1 [H1 H2]]. {
        intros Habsurd. now inversion Habsurd.
      }
      subst.
      destruct (pick_cons H2) as [vm2_out_rq2 [H1 H3]]. {
        specialize (Fresh.make_valid_not_equal pid1 pid2 new_pid1 vm0_out_rc new_pid1_rc Hvalid_pid2 Hnew_pid1_rc_valid) as H.
        intros Habsurd. now inversion Habsurd.
      }
      subst.
      destruct (pick_two Hvm0_pick H3) as [vm0_out' [vm2_out_rq2' [Hvm2_out' [Hpick_0' Hvm2_out_rq2'_equiv]]]].
      apply pick_app_rev with (new := [{| pid := pid2; proc_mb_t := mb_t2; cont := cont2 {| mba_pid := new_pid2 |} |};
                                       {| pid := new_pid2; proc_mb_t := child_mb_t2; cont := child2 |}]) in Hpick_0'.
      (* Run queue: *)
      set (rq' :=
             [{| pid := pid1; proc_mb_t := mb_t1; cont := cont1 {| mba_pid := new_pid1 |} |};
               {| pid := new_pid1; proc_mb_t := child_mb_t1; cont := child1 |};
               {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 {| mba_pid := new_pid2 |} |};
               {| pid := new_pid2; proc_mb_t := child_mb_t2; cont := child2 |}]
               ++ vm2_out_rq2').
      (* World: *)
      set (w' := h_spawn new_pid1 child_mb_t1 (h_spawn new_pid2 child_mb_t2 vm0_out_w)).
      (* Run queue invariant: *)
      destruct (Fresh.swap_make pid1 pid2 new_pid1 new_pid2 vm0_out_rc new_pid1_rc new_pid2_rc Hpids12 Hnew_pid1_rc_valid Hnew_pid2_rc_valid) as [rc2' [rc3' [Hrc' [Hnew_pid1' Hnew_pid2']]]].
      assert (Hvm_pids_valid : Forall (proc_valid_pid rc3') rq'). {
        subst rq'.
        rewrite Hvm2_out_rq2'_equiv.
        solve_rc_invariant.
      }
      (* Build it: *)
      exists {|
          world := w';
          runq := rq';
          ref_ctr := rc3';
          inv_valid_pids := Hvm_pids_valid;
        |}. split.
      2:{ split > [|split].
          - simpl. subst w'.
            apply h_spawn_commutativity.
            apply Fresh.new2_not_equal with (p1 := pid2) (p2 := pid1) (rc := vm0_out_rc) (rc' := rc2') (rc'' := rc3'); try assumption.
            symmetry. assumption.
          - now symmetry.
          - subst rq'.
            eapply Permutation_swap2; eauto.
            now symmetry.
      } {
        simpl.
        set (rq_ := {| pid := pid2; proc_mb_t := mb_t2; cont := cont2 {| mba_pid := new_pid2 |} |}
                      :: {| pid := new_pid2; proc_mb_t := child_mb_t2; cont := child2 |}
                      ::  vm0_out') in *.
        assert (Hinv_rc2'' :  Forall (proc_valid_pid vm0_out_rc) vm0_out') by solve_rc_invariant.
        assert (Hinv_rc2' : Forall (proc_valid_pid rc2') rq_). {
          subst rq_.
          solve_rc_invariant.
        }
        exists {|
            world := h_spawn new_pid2 child_mb_t2 vm0_out_w;
            runq := rq_;
            ref_ctr := rc2';
            inv_valid_pids := Hinv_rc2';
          |}.
        split.
        - solve_vm_step ().
          + sauto.
          + solve_alloc_pid. sauto.
        - solve_vm_step ().
          + solve_rc_invariant.
          + sauto.
          + solve_alloc_pid. sauto.
      }
  Qed.
End commute.
