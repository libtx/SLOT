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
  IOHandler.

From LibTx Require Import
  Storage
  Storage.Properties.

Import Setoids TransitionSystem ListSelector Ref.FMap.
Export Ref IOHandler.

From Hammer Require Import
  Hammer.

From RecordUpdate Require Import
  RecordUpdate.

Open Scope positive_scope.

Set Hammer Debug.
Set Hammer ATPLimit 100.
Set Hammer GSMode 64.

Opaque put.
Opaque get.

Infix "=h=" := (@equiv _ h_setoid) (at level 50) : slot_scope.

Open Scope slot_scope.

Section VM.
  Context `{IOH : IOHandler}.

  Let World := @h_state _ _ IOH.

  Let Heqiv_w := @h_setoid _ _ IOH.

  CoInductive Program (Mailbox : Set) : Type :=
  | die : (* Program termintes *)
      Program Mailbox
  | p_yield :
    (** Interrupt the computation without producing any side effects.

        This primitive is used to softly introduce the concept of
        Erlang's "reductions", and to side-step termination checker,
        making programs non-Turing in a practically useful, as opposed
        to forced, way.

        In Erlang, reduction counting improves responsiveness of the
        system, in SLOT it *additionally* gives a structural argument
        "for free". *)
    forall (continuation : Program Mailbox),
      Program Mailbox
  | p_io : (* Program is doing I/O *)
    forall (pending_req : Request)
      (continuation : Reply pending_req -> Program Mailbox),
      Program Mailbox
  | p_spawn : (* Spawn a new process: *)
    forall {Mailbox' : Set}
      (child : @Program Mailbox')
      (continuation : @Address Mailbox' -> Program Mailbox),
      Program Mailbox.

  Record Process :=
    mkProcess
      { pid : Ref;
        proc_mb_t : Set;
        cont : @Program proc_mb_t;
      }.

  #[export] Instance etaProc : Settable _ := settable! mkProcess <pid; proc_mb_t; cont>.

  Record VM :=
    mkVM
      { (* State of the I/O handler *)
        world : World;
        (* Set of runnable processes *)
        runq : list Process;
        (* Counter that gets incremented when process spawns a child.
        This counter is used as a suffix of the child's pid *)
        ref_ctr : Ref.FMap.M.t positive;
      }.

  #[export] Instance etaVM : Settable _ := settable! mkVM <world; runq; ref_ctr>.

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

  Definition make_ref (parent : Ref) (v : VM) : VM * Ref :=
    let cc := ref_ctr v in
    let (cc, ctr) :=
      match get parent cc with
      | Some ctr =>
          (put parent (ctr + 1) cc, ctr)
      | None =>
          (put parent 2 cc, 1)
      end in
    (v<| ref_ctr := cc |>, parent ++ [ctr]).

  Lemma make_ref_commut vm r1 r2 vm1' vm1'' vm2' vm2'' r11 r12 r21 r22 :
    r1 <> r2 ->
    make_ref r1 vm = (vm1', r11) ->
    make_ref r2 vm1' = (vm1'', r12) ->
    make_ref r2 vm = (vm2', r22) ->
    make_ref r1 vm2' = (vm2'', r21) ->
    r11 = r21 /\ r12 = r22 /\ vm1'' == vm2''.
  Proof.
    intros Hr12 H11 H12 H21 H22.
    unfold make_ref in *.
    replace (get r2 (ref_ctr vm1')) with (get r2 (ref_ctr vm)) in H12 by sauto use:distinct.
    replace (get r1 (ref_ctr vm2')) with (get r1 (ref_ctr vm)) in H22 by sauto use:distinct.
    repeat split.
    - sauto.
    - sauto.
    - destruct (get r1 (ref_ctr vm)); destruct (get r2 (ref_ctr vm));
        repeat lazymatch goal with
          | [H : (?a, ?b) = (?c, ?d) |- _] =>
              let H1 := fresh H "_vm" in
              let H2 := fresh H "_ref" in
              apply pair_equal_spec in H; destruct H as [H1 H2]
          end;
        subst;
        repeat split;
        try reflexivity;
        now apply put_distict_comm.
  Qed.

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
    exists (ret', {| world := w2'; runq := rq1'; ref_ctr := rc1'|}).
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
    exists {| world := w2'; runq := rq1'; ref_ctr := rc1'|}.
    repeat split; try assumption.
    - apply Hrc.
  Qed.

  Global Instance vmIOHandlerBlocks : @IOHandlerBlocks VM World vm_setoid.
  Proof.
    split.
    - intros Ret State Heqiv_r Hequiv_w w_morph.
  Abort.

  Definition do_spawn {Mailbox : Set} (parent : Ref) (prog : @Program Mailbox) (v : VM) : (Ref * VM) :=
    let (v, new_pid) := make_ref parent v in
    let rq := runq v in
    let new_process := {|
                        pid := new_pid;
                        proc_mb_t := Mailbox;
                        cont := prog
                       |} in
    let w' := h_spawn new_pid Mailbox (world v) in
    (new_pid, v<| runq := new_process :: rq|> <|world := w'|>).

  Definition initVm {Mailbox : Set} (p : @Program Mailbox) :=
    let vm :=
      {|
        world := h_initial;
        runq := [];
        ref_ctr := new;
      |} in
    let (_, vm) := do_spawn [] p vm in
    vm.

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

  Definition vm_process_die pid : MFun VM VM :=
    lift_w (h_terminate pid).

  Section run_queue_mgmt.
    Context {IORet} Mailbox (pid_ : Ref) (next : IORet -> Program Mailbox).

    Definition vm_handle_io_reply : MFun (IORet * VM) VM :=
      let morph (ret : IORet * VM) :=
        let (ret, vm) := ret in
        let proc := {| pid := pid_; proc_mb_t := Mailbox; cont := next ret |} in
        vm <| runq := proc :: runq vm |>
      in
      pure morph ltac:(sauto).
  End run_queue_mgmt.

  Definition vm_process_io (pid : Ref) mb_t (req : Request) (next : Reply req -> Program mb_t) : MFun VM VM :=
    vm_handle_io_reply mb_t pid next ∘ lift_w_ret (h_handler pid req).

  Definition vm_push_proc (proc : Process) : MFun VM VM :=
    let morph vm :=
      vm <| runq := proc :: runq vm |>
    in
    pure morph ltac:(sauto).

  (* TODO: rewrite as composition of mfuns *)
  Definition process_spawn_morph pid mb_t child_mb_t (child_prog : Program child_mb_t) (next : @Address child_mb_t -> Program mb_t) vm vm' :=
    let (child_pid, vm) := do_spawn pid child_prog vm in
    let addr := mkAddress child_mb_t child_pid in
    let proc := {| pid := pid; proc_mb_t := mb_t; cont := next addr |} in
    vm' = vm <| runq := proc :: (runq vm) |>.

  Lemma process_spawn_morph_covariance pid mb_t
    child_mb_t (child_prog : Program child_mb_t)
    (next : @Address child_mb_t -> Program mb_t) vm1 vm1' vm2 :
    vm1 == vm1' ->
    process_spawn_morph pid mb_t child_mb_t child_prog next vm1 vm2 ->
    exists{vm2' == vm2}, process_spawn_morph pid mb_t child_mb_t child_prog next vm1' vm2'.
  Proof.
    unfold process_spawn_morph, do_spawn, equiv, vm_setoid.
    destruct vm1 as [w1 rq1 rc1].
    destruct vm1' as [w1' rq1' rc1'].
    destruct vm2 as [w2 rq2 rc2].
    intros Hvm1 Hvm2.
    destruct Hvm1 as [Hw1 [Hrc1 Hrq1]].
    remember (make_ref pid {| world := w1; runq := rq1; ref_ctr := rc1 |}) as Hchild_pid.
    destruct Hchild_pid as [vm3 child_pid].
    destruct vm3 as [w3 rq3 rc3].
    inversion_clear Hvm2.
    remember (make_ref pid {| world := w1'; runq := rq1'; ref_ctr := rc1' |}) as Hchild_pid'.
    destruct Hchild_pid' as [[w3' rq3' rc3'] child_pid'].
    assert (w3' =h= w3 /\ rq3 =p= rq3' /\ rc3 == rc3' /\ child_pid = child_pid') as H. {
      unfold make_ref in *.
      simpl in HeqHchild_pid. simpl in HeqHchild_pid'. rewrite <-Hrc1 in HeqHchild_pid'.
      destruct (get pid rc1);
        inversion_clear HeqHchild_pid;
        inversion_clear HeqHchild_pid'.
      - split; [|split; [|split]].
        + now rewrite Hw1.
        + now rewrite Hrq1.
        + rewrite Hrc1; sauto.
        + reflexivity.
      - split; [|split; [|split]].
        + now rewrite Hw1.
        + now rewrite Hrq1.
        + rewrite Hrc1; sauto.
        + reflexivity.
    }
    destruct H as [Hw3 [Hrq3 [Hrc3 Hchild_pid]]]. subst.
    exists {|
        world := h_spawn child_pid' child_mb_t w3';
        runq := {| pid := pid; proc_mb_t := mb_t; cont := next {| mba_pid := child_pid' |} |}
                  :: {| pid := child_pid'; proc_mb_t := child_mb_t; cont := child_prog |}
                  :: rq3';
        ref_ctr := rc3';
      |}.
    simpl. split; [|split; [|split]].
    - reflexivity.
    - symmetry in Hw3.
      now apply (h_spawn_covariance child_pid' child_mb_t w3 w3').
    - assumption.
    - constructor. constructor. apply Hrq3.
  Qed.

  Definition exec_proc (proc : Process) : MFun VM VM :=
    match proc with
      {| pid := pid; proc_mb_t := mb_t; cont := prog |} =>
        match prog with
        | die _ =>
            vm_process_die pid
        | p_yield _ next =>
            vm_push_proc {| pid := pid; proc_mb_t := mb_t; cont := next |}
        | p_io _ req next =>
            vm_process_io pid mb_t req next
        | @p_spawn _ child_mb_t child_prog next =>
            {|
              morphism := process_spawn_morph pid mb_t child_mb_t child_prog next;
              morphism_covariance := process_spawn_morph_covariance _ _ _ _ _
            |}
        end
    end.

  Inductive vm_state_trans_morph : VM -> @ts_ret VM Process -> Prop :=
  | vm_state_trans_morph_none : forall w rc,
      vm_state_trans_morph
        {| world := w; ref_ctr := rc; runq := [] |}
        None
  | vm_state_trans_morph_some : forall w rc rq1 rq2 proc vm3,
      Pick rq1 proc rq2 ->
      {| world := w; runq := rq2; ref_ctr := rc |} ~[exec_proc proc]~> vm3 ->
      vm_state_trans_morph
        {| world := w; ref_ctr := rc; runq := rq1 |}
        (Some (proc, vm3)).

  Lemma vm_state_trans_morph_covariance vm1 vm1' (ret : @ts_ret VM Process) :
    vm1 == vm1' ->
    vm_state_trans_morph vm1 ret ->
    exists{ret' == ret}, vm_state_trans_morph vm1' ret'.
  Proof.
    intros Hvm Hret.
    destruct vm1 as [w1 rq1 rc1].
    destruct vm1' as [w1' rq1' rc1'].
    destruct Hvm as [Hw1 [Hrc1 Hrq1]].
    inversion Hret as [|? ? ? rq2 proc vm3 Hrq2 Hvm3]; subst.
    - exists None.
      unfold equiv, vm_setoid in *.
      apply Permutation_nil in Hrq1. sauto.
    - apply pick_equiv with (l1' := rq1') in Hrq2; [|assumption].
      destruct Hrq2 as [rq2' [Hrq2' Hrq2]].
      apply morphism_covariance with (x' := {| world := w1'; runq := rq2'; ref_ctr := rc1'|}) in Hvm3; [|sauto].
      destruct Hvm3 as [vm3' [Hvm3' Hvm3]].
      exists (Some (proc, vm3')).
      split.
      + apply vm_state_trans_morph_some with (rq2 := rq2'); assumption.
      + sauto.
  Qed.

  Definition vm_state_trans : MFun VM (@ts_ret VM Process) :=
    {|
      morphism := vm_state_trans_morph;
      morphism_covariance := vm_state_trans_morph_covariance;
    |}.

  Global Instance vmTransitionSystem : @TransitionSystem VM Process :=
    { ts_state_trans := vm_state_trans;
    }.
End VM.

Global Arguments VM {_ _} _.
Global Arguments die {_ _ _}.
Global Arguments p_yield {_ _ _}.
Global Arguments p_io {_ _ _}.
Global Arguments p_spawn {_ _ _ _}.
Global Arguments initVm {_ _} _ {_}.

From Ltac2 Require
  Fresh
  String
  Ident.
From Ltac2 Require Import
  Notations
  Printf.

Set Default Proof Mode "Ltac2".

Ltac2 fresh_id str := Fresh.in_goal (Option.get (Ident.of_string str)).

Ltac2 unfold_vm_hyp (hyp : Init.constr) :=
  match Constr.Unsafe.kind hyp with
  | Constr.Unsafe.Var hyp_id =>
      let vm_id := Ident.to_string hyp_id in
      let w := fresh_id (String.app vm_id "_w") in
      let runq := fresh_id (String.app vm_id "_rq") in
      let refctr := fresh_id (String.app vm_id "_rc") in
      destruct $hyp as [$w $runq $refctr]
  | _ => ()
  end.

Ltac2 unfold_proc_hyp (hyp : Init.constr) :=
  match Constr.Unsafe.kind hyp with
  | Constr.Unsafe.Var hyp_id =>
      let proc_id := Ident.to_string hyp_id in
      let pid := fresh_id (String.app proc_id "_pid") in
      let mb_t := fresh_id (String.app proc_id "_mb_t") in
      let cont := fresh_id (String.app proc_id "_cont") in
      destruct $hyp as [$pid $mb_t $cont]
  | _ => ()
  end.

Ltac2 step_vm_morph (hyp_id : Ident.t) :=
  let hyp := Control.hyp hyp_id in
  lazy_match! Constr.type hyp with
  | vm_state_trans_morph ?vm (Some (?proc, ?vm')) =>
      let (h_proc, h_pick, rq)
        := match Constr.Unsafe.kind proc with
           | Constr.Unsafe.Var h_proc_id =>
               let h_proc_id := Ident.to_string h_proc_id in
               ( fresh_id (String.app "H_exec_" h_proc_id),
                 fresh_id (String.app "H_pick_" h_proc_id),
                 fresh_id (String.app "rq_wo_" h_proc_id)
               )
           | _ =>
               ( fresh_id "H_exec",
                 fresh_id "H_pick",
                 fresh_id "rq_"
               )
           end in
      unfold_vm_hyp vm;
      unfold_vm_hyp vm';
      unfold_proc_hyp proc;
      inversion_clear $hyp as [|? ? ? $rq ? ? $h_pick $h_proc]
  end.

Section tests.
  Context `{HIOh : IOHandler}.
  Goal forall vm1 vm2 proc,
      vm_state_trans_morph vm1 (Some (proc, vm2)) ->
      False.
    intros.
    step_vm_morph @H.
    match! goal with
    | [ h1 : Pick _ ?proc _, h2 : _ ~[exec_proc ?proc]~> _ |- _ ] =>
        ()
    end.
  Abort.
End tests.

Section commut.
  Context `{IOH : IOHandler} {mbt1 mbt2 : Set} {pid1 pid2 : Ref}.

  Lemma yield_yield_commut cont1 cont2 :
    pid1 <> pid2 ->
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := @p_yield _ _ mbt1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := @p_yield _ _ mbt2 cont2 |}.
  Proof.
(*    intros Hpids vm1 vm3.
    simpl; split; intros H; destruct H as [vm2 [Hvm2 Hvm3]].
    - step_vm_morph @Hvm2.
      inversion H_exec. subst. clear H_exec.
      step_vm_morph @Hvm3.
      inversion H_exec. subst. clear H_exec.
      apply pick_cons in H_pick0 > [|intros Habsurd; now inversion Habsurd].
      destruct H_pick0 as [rq_0' [Hrq_0' H_pick0]].
      destruct (pick_two H_pick H_pick0) as [rq1' [rq2' [Hrq1' [Hrq2' Hrqs]]]].
      subst.
      exists {| world := vm1_w;
          runq := {| pid := pid1; proc_mb_t := mbt1; cont := cont1 |}
                :: {| pid := pid2; proc_mb_t := mbt2; cont := cont2 |}
                :: rq2';
          ref_ctr := vm1_rc
        |}.
      split.
      + exists {| world := vm1_w;
            runq := {| pid := pid2; proc_mb_t := mbt2; cont := cont2 |} :: rq1';
            ref_ctr := vm1_rc
          |}.
        ltac1:(sauto).
      + simpl. repeat split; try ltac1:(easy).
        now rewrite perm_swap, Hrqs.
    - step_vm_morph @Hvm2.
      inversion H_exec. subst. clear H_exec.
      step_vm_morph @Hvm3.
      inversion H_exec. subst. clear H_exec.
      apply pick_cons in H_pick0 > [| intros Habsurd; inversion Habsurd; now symmetry in H0 ].
      destruct H_pick0 as [rq_0' [Hrq_0' H_pick0]].
      destruct (pick_two H_pick H_pick0) as [rq1' [rq2' [Hrq1' [Hrq2' Hrqs]]]].
      subst.
      exists {| world := vm1_w;
          runq := {| pid := pid2; proc_mb_t := mbt2; cont := cont2 |}
                :: {| pid := pid1; proc_mb_t := mbt1; cont := cont1 |}
                :: rq2';
          ref_ctr := vm1_rc
        |}.
      split.
      + exists {| world := vm1_w;
            runq := {| pid := pid1; proc_mb_t := mbt1; cont := cont1 |} :: rq1';
            ref_ctr := vm1_rc
          |}.
        ltac1:(sauto).
      + simpl. repeat split; try ltac1:(easy).
        now rewrite perm_swap, Hrqs.
  Qed.*)
    Abort.
End commut.

Require Import Handlers.Mailbox.

(* begin details *)
Notation "'do' V '<-' I ; C" := (p_io (I) (fun V => C))
    (at level 100, C at next level, V name, right associativity) : slot_scope.

Notation "'call' V '<-' I ; C" := (I (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, C at next level, V ident,
    right associativity) : slot_scope.

Notation "P '!' M ; C" := (p_io (send P (appmsg M)) (fun _ => C))
    (at level 99, C at next level, right associativity) : slot_scope.
(* end details *)

Definition prog_t `(IOHandler) mb_t :=
  @Program Request Reply mb_t.

Section test.
  Let h := mailboxHandler.
  Let VM := VM h.

  Let child1 : prog_t h positive := die.

  Let child2 : prog_t h bool := die.

  Fail Let prog : prog_t h True :=
        spawn c1 <- child1;
        c1 ! 1;
        spawn c2 <- child2;
        c2 ! 1;
        die.

  Let prog : prog_t h True :=
        spawn c1 <- child1;
        c1 ! 1;
        spawn c2 <- child2;
        c2 ! false;
        die.

  Let vm := initVm h prog.

  Goal forall t vm', TSMFunGen vm t vm' ->
                CanonicalTrace t vm vm' ->
                True.
    intros t vm' Ht Hcanon.
    subst vm prog.
    inversion Ht; subst.
    - inversion_clear H.
    - unfold initVm, do_spawn in H0.
  Abort.
End test.
