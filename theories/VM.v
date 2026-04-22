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

Set Hammer Debug.
Set Hammer ATPLimit 100.
Set Hammer GSMode 4.

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
        ref_ctr : Ref.FMap.M.t positive;
      }.

  (* begin hide *)
  #[export] Instance etaVM : Settable _ := settable! mkVM <world; runq; ref_ctr>.
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

  Definition make_ref (parent : Ref) (v : VM) : Ref * VM :=
    let cc := ref_ctr v in
    let (cc, ctr) :=
      match get parent cc with
      | Some ctr =>
          (put parent (ctr + 1) cc, ctr)
      | None =>
          (put parent 2 cc, 1)
      end in
    (parent ++ [ctr], v<| ref_ctr := cc |>).

  Lemma make_ref_commut vm r1 r2 vm1' vm1'' vm2' vm2'' r11 r12 r21 r22 :
    r1 <> r2 ->
    make_ref r1 vm = (r11, vm1') ->
    make_ref r2 vm1' = (r12, vm1'') ->
    make_ref r2 vm = (r22, vm2') ->
    make_ref r1 vm2' = (r21, vm2'') ->
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

  Definition do_spawn {Mailbox : Set} (parent : Ref) (prog : @Program Mailbox) (v : VM) : (Ref * VM) :=
    let (new_pid, v) := make_ref parent v in
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

    Program Definition vm_handle_io_reply : MFun (IORet * VM) VM :=
      let morph (ret : IORet * VM) :=
        let (ret, vm) := ret in
        let proc := {| pid := pid_; proc_mb_t := Mailbox; cont := next ret |} in
        vm <| runq := proc :: runq vm |>
      in
      pure morph _.
    Next Obligation.
      sauto.
    Qed.
  End run_queue_mgmt.

  Definition vm_process_io (pid : Ref) mb_t (req : Request) (next : Reply req -> Program mb_t) : MFun VM VM :=
    vm_handle_io_reply mb_t pid next ∘ lift_w_ret (h_handler pid req).

  Definition maybe_proc_vm := option (Process * VM).

  Program Definition schedule_in (proc : Process) : MFun VM VM :=
    pure (fun vm => vm <| runq := proc :: runq vm |>) _.
  Next Obligation.
    sauto.
  Qed.

  Inductive ScheduleOutOption : VM -> maybe_proc_vm -> Prop :=
  | ScheduleOut_Some : forall w refc runq runq' proc,
      runq ~[pick_mfun_option]~> (Some (proc, runq')) ->
      ScheduleOutOption
        {| world := w; ref_ctr := refc; runq := runq |}
        (Some (proc, {| world := w; ref_ctr := refc; runq := runq' |}))
  | ScheduleOut_None : forall w refc,
      ScheduleOutOption
        {| world := w; ref_ctr := refc; runq := [] |}
        None.

  Program Definition schedule_out : MFun VM maybe_proc_vm :=
    {| morphism := ScheduleOutOption |}.
  Next Obligation.
    unfold exists_equiv.
    destruct x as [w rq1 rc].
    destruct x' as [w' rq1' rc'].
    destruct H as [Heq_w [Heq_refc Heq_runq]].
    inversion H0; subst.
    - apply morphism_covariance with (x' := rq1') in H4; [|assumption].
      sauto.
    - apply Permutation_nil in Heq_runq. subst.
      sauto.
  Qed.

  Inductive ScheduleOutCertain proc : VM -> VM -> Prop :=
  | ScheduleOutCertain_ : forall w refc runq runq',
      runq ~[pick_certain_mfun proc]~> runq' ->
      ScheduleOutCertain
        proc
        {| world := w; ref_ctr := refc; runq := runq |}
        {| world := w; ref_ctr := refc; runq := runq' |}.

  Program Definition schedule_out_certain proc :=
    {| morphism := ScheduleOutCertain proc |}.
  Next Obligation.
    destruct x as [w1 rq1 rc1].
    destruct x' as [w1' rq1' rc1'].
    destruct y as [w2 rq2 rc2].
    destruct H as [Hw [Hrc Hrq]].
    inversion H0; subst.
    apply morphism_covariance with (x' := rq1') in H1; [|assumption].
    destruct H1 as [rq2' [Hrq2' Hrq2rq2']].
    exists {| world := w1'; ref_ctr := rc1'; runq := rq2' |}.
    sauto.
  Qed.

  Lemma schedule_out_certain_commute proc1 proc2 :
    pid proc1 <> pid proc2 ->
    commute (schedule_out_certain proc1) (schedule_out_certain proc2).
  Proof.
    intros Hpids.
    intros vm1 vm3; split; simpl;
      intros [vm2 [Hvm2 Hvm3]].
    - inversion Hvm2 as [w1 rc1 rq1 rq2 Hproc1]; subst; clear Hvm2.
      inversion Hvm3 as [? ? ? rq3 Hproc2]; subst; clear Hvm3.
      simpl in *.
      destruct (pick_two Hproc1 Hproc2) as [rq2' [rq3' [Hrq2' [Hrq3' Heq]]]].
      exists {| world := w1; ref_ctr := rc1; runq := rq3' |}.
      split.
      2:{ simpl. rewrite Heq. sauto. }
      exists {| world := w1; ref_ctr := rc1; runq := rq2' |}.
      sauto.
    - inversion Hvm2 as [w1 rc1 rq1 rq2 Hproc2]; subst; clear Hvm2.
      inversion Hvm3 as [? ? ? rq3 Hproc1]; subst; clear Hvm3.
      simpl in *.
      destruct (pick_two Hproc2 Hproc1) as [rq2' [rq3' [Hrq2' [Hrq3' Heq]]]].
      exists {| world := w1; ref_ctr := rc1; runq := rq3' |}.
      split.
      2:{ simpl. rewrite Heq. sauto. }
      exists {| world := w1; ref_ctr := rc1; runq := rq2' |}.
      sauto.
  Qed.

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
    destruct Hchild_pid as [child_pid vm3].
    destruct vm3 as [w3 rq3 rc3].
    inversion_clear Hvm2.
    remember (make_ref pid {| world := w1'; runq := rq1'; ref_ctr := rc1' |}) as Hchild_pid'.
    destruct Hchild_pid' as [child_pid' [w3' rq3' rc3']].
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
            schedule_in {| pid := pid; proc_mb_t := mb_t; cont := next |}
        | p_io _ req next =>
            vm_process_io pid mb_t req next
        | @p_spawn _ child_mb_t child_prog next =>
            {|
              morphism := process_spawn_morph pid mb_t child_mb_t child_prog next;
              morphism_covariance := process_spawn_morph_covariance _ _ _ _ _
            |}
        end
    end.

  Lemma exec_proc_schedule_commute proc1 proc2 :
    pid proc1 <> pid proc2 ->
    commute (exec_proc proc1) (schedule_out_certain proc2).
  Proof.
    intros Hpids.
    destruct proc1 as [pid1 mb_t1 cont1].
    intros [w1 rq1 rc1] [w3 rq3 rc3]; split;
      intros [[w2 rq2 rc2] [Hvm2 Hvm3]].
    - inversion Hvm3 as [? ? ? ? Hvm3_]; subst; clear Hvm3.
      unfold exists_equiv.
      destruct cont1.
      + destruct Hvm2 as [Hw [Hrc Hrq]]. subst.
        exists {| world := w3; runq := rq3; ref_ctr := rc3 |}.
        split; [|easy].
        unfold exec_proc, vm_process_die.
        exists {| world := w1; runq := rq3; ref_ctr := rc3 |}.
        sauto.
      + inversion Hvm2; subst; clear Hvm2.
        simpl in Hvm3_.
        apply pick_cons in Hvm3_; [|sauto].
        destruct Hvm3_ as [rq2 [? Hrq2]]. subst.
        exists {|
            world := w3;
            ref_ctr := rc3;
            runq := {| pid := pid1; proc_mb_t := mb_t1; cont := cont1 |} :: rq2
          |}.
        split; [|sauto].
        exists {| world := w3; ref_ctr := rc3; runq := rq2 |}.
        sauto.
      + inversion Hvm2; subst; clear Hvm2.
        destruct x as [iorepl vm2].
        destruct H as [Hvm2 Hcont].
        inversion Hcont; subst; clear Hcont.
        apply pick_cons in Hvm3_.
        2:{ sauto. }
        destruct Hvm3_ as [rq3' [Hrq3' Hpick]]. subst.
        destruct vm2 as [w2 rq2 rc2].
        destruct Hvm2 as [Hrepl [Hrq Hrc]]. subst.
        exists {|
            world := w2;
            ref_ctr := rc2;
            runq := {| pid := pid1; proc_mb_t := mb_t1; cont := continuation iorepl |} :: rq3';
          |}.
        split.
        * unfold exec_proc.
          exists {| world := w1; ref_ctr := rc2; runq := rq3' |}.
          split.
          -- sauto.
          -- unfold vm_process_io.
             exists (iorepl, {| world := w2; ref_ctr:= rc2; runq := rq3' |}).
             sauto.
        * sauto.
      + unfold exec_proc, process_spawn_morph in Hvm2. simpl in Hvm2.
        simpl in Hvm3_.
        unfold do_spawn in Hvm2.
  Admitted.

  Inductive exec_proc_pair_morph : maybe_proc_vm -> maybe_proc_vm -> Prop :=
  | exec_proc_pair_morph_none :
    exec_proc_pair_morph None None
  | exec_proc_pair_morph_some : forall proc vm vm',
      vm ~[exec_proc proc]~> vm' ->
      exec_proc_pair_morph (Some (proc, vm)) (Some (proc, vm')).

  Lemma exec_proc_pair_morph_covariance : forall x x' y : maybe_proc_vm,
      x == x' ->
      exec_proc_pair_morph x y -> (exists{ y' == y}, exec_proc_pair_morph x' y').
  Proof.
    intros x x' y Hxx' Hxy.
    destruct x.
    - inversion Hxy; subst; clear Hxy.
      destruct x' as [[proc_ vm_]|].
      + unfold equiv, setoid_option, equiv, pair_setoid in Hxx'.
        destruct Hxx' as [Hproc_ Hvm_].
        morph_shift (exec_proc proc) vm_.
        exists (Some (proc, vm'')).
        sauto.
      + inversion Hxx'.
    - inversion_clear Hxy.
      exists None.
      sauto.
  Qed.

  Definition exec_proc' : MFun maybe_proc_vm maybe_proc_vm :=
    {|
      morphism := exec_proc_pair_morph;
      morphism_covariance := exec_proc_pair_morph_covariance;
    |}.

  Definition vm_state_trans : MFun VM maybe_proc_vm :=
    exec_proc' ∘ schedule_out.

  Lemma vm_pick_simplify proc vm1 vm3 :
    Some (proc, vm3) <~[exec_proc' ∘ schedule_out]~ vm1 <->
      vm3 <~[exec_proc proc ∘ schedule_out_certain proc]~ vm1.
  Proof.
    split; intros [x2 [Hx2 Hvm3]].
    - inversion Hvm3; subst; clear Hvm3.
      inversion Hx2; subst; clear Hx2.
      inversion H2; subst; clear H2.
      exists {| world := w; runq := runq'; ref_ctr := refc |}.
      sauto.
    - inversion Hx2; subst; clear Hx2.
      simpl in H.
      exists (Some (proc, {| world := w; runq := runq'; ref_ctr := refc |})).
      sauto.
  Qed.

  Global Instance vmTransitionSystem : @TransitionSystem VM Process :=
    { ts_state_trans := vm_state_trans;
    }.

  (* begin hide *)
  Lemma commute_swap0 f g h i a e :
    commute h g ->
    e <~[h ∘ g ∘ f ∘ i]~ a ->
    exists{e' == e}, e' <~[g ∘ h ∘ f ∘ i]~ a.
  Proof.
    intros Hgh Hz.
    apply mfun_assoc in Hz.
    destruct Hz as [c [Hc He]].
    specialize (Hgh c e).
    apply Hgh in He.
    destruct He as [e' [Hce' Hee']].
    exists e'. split; [|assumption].
    apply mfun_assoc.
    exists c. sauto.
  Qed.

  Lemma commute_swap1 f g h i a e :
    commute g h ->
    e <~[i ∘ h ∘ g ∘ f]~ a ->
    exists{e' == e}, e' <~[i ∘ g ∘ h ∘ f]~ a.
  Proof.
    intros Hgh [b [Hb He]].
    apply mfun_assoc in He.
    destruct He as [d [Hd He]].
    apply Hgh in Hd.
    destruct Hd as [d' [Hbd' Hdd']].
    morph_shift i d'.
    exists e'. split; [|assumption].
    exists b. split; [assumption|].
    apply mfun_assoc.
    exists d'. sauto.
  Qed.

  Lemma commute_swap2 f g h i a e :
    commute f g ->
    e <~[i ∘ h ∘ g ∘ f]~ a ->
    exists{e' == e}, e' <~[i ∘ h ∘ f ∘ g]~ a.
  Proof.
    intros Hfg Hae.
    apply mfun_assoc in Hae.
    destruct Hae as [d [Hd He]].
    apply Hfg in Hd.
    destruct Hd as [d' [Had' Hdd']].
    morph_shift (i ∘ h) d'.
    exists e'.
    split; [|assumption].
    apply mfun_assoc.
    sauto.
  Qed.

  Ltac unfold_vm_microsteps :=
    repeat match goal with
      | [H : ?vm' <~[?a ∘ ?b]~ ?vm |- _ ] =>
          let vm_ := fresh vm in
          let H_ := fresh H in
          destruct H as [vm_ [H H_]]
      end.

  Ltac vm_microstep_commute :=
    lazymatch goal with
    | [ |- commute (exec_proc ?proc1) (schedule_out_certain ?proc2) ] =>
        now apply exec_proc_schedule_commute
    | [ |- commute (schedule_out_certain ?proc2) (exec_proc ?proc1) ] =>
        now apply commute_sym, exec_proc_schedule_commute
    | [ |- commute (schedule_out_certain ?proc1) (schedule_out_certain ?proc2) ] =>
        now apply schedule_out_certain_commute
    | _ =>
        first [assumption | now apply commute_sym]
    end.
  (* end hide *)

  Lemma vm_exec_commute proc1 proc2 :
    pid proc1 <> pid proc2 ->
    commute (exec_proc proc1) (exec_proc proc2) ->
    event_commute proc1 proc2.
  Proof.
    intros Hprocs Hexec_comm.
    unfold event_commute, tm_state_trans, tsTokenSystem.
    unfold ts_mfun, ts_state_trans, vmTransitionSystem, vm_state_trans.
    intros vm0 vm4; split; intros [vm1 [Hvm1 Hvm4]].
    - rewrite (vm_pick_simplify proc1 vm0 vm1) in Hvm1.
      rewrite (vm_pick_simplify proc2 vm1 vm4) in Hvm4.
      assert (Hvm04 : vm4 <~[exec_proc proc2 ∘ schedule_out_certain proc2 ∘ exec_proc proc1 ∘ schedule_out_certain proc1]~ vm0) by sauto.
      clear Hvm1. clear Hvm4.
      apply commute_swap1 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4' [Hvm04 Hequiv1]].
      apply commute_swap0 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4'' [Hvm04 Hequiv2]].
      apply commute_swap2 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4''' [Hvm04 Hequiv3]].
      apply commute_swap1 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4'''' [Hvm04 Hequiv4]].
      exists vm4''''.
      split.
      + clear Hequiv1. clear Hequiv2. clear Hequiv3. clear Hequiv4. clear vm1. clear vm4.
        rename vm4'''' into vm5.
        simpl.
        unfold_vm_microsteps.
        exists vm2. split.
        * exists (Some (proc2, vm1)). sauto.
        * exists (Some (proc1, vm3)). sauto.
      + now rewrite Hequiv1, Hequiv2, Hequiv3, Hequiv4.
    - rewrite (vm_pick_simplify proc2 vm0 vm1) in Hvm1.
      rewrite (vm_pick_simplify proc1 vm1 vm4) in Hvm4.
      assert (Hvm04 : vm4 <~[exec_proc proc1 ∘ schedule_out_certain proc1 ∘ exec_proc proc2 ∘ schedule_out_certain proc2]~ vm0) by sauto.
      clear Hvm1. clear Hvm4.
      apply commute_swap1 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4' [Hvm04 Hequiv1]].
      apply commute_swap0 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4'' [Hvm04 Hequiv2]].
      apply commute_swap2 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4''' [Hvm04 Hequiv3]].
      apply commute_swap1 in Hvm04; [|vm_microstep_commute].
      destruct Hvm04 as [vm4'''' [Hvm04 Hequiv4]].
      exists vm4''''.
      split.
      + clear Hequiv1. clear Hequiv2. clear Hequiv3. clear Hequiv4. clear vm1. clear vm4.
        rename vm4'''' into vm5.
        simpl.
        unfold_vm_microsteps.
        exists vm2. split.
        * exists (Some (proc1, vm1)). sauto.
        * exists (Some (proc2, vm3)). sauto.
      + now rewrite Hequiv1, Hequiv2, Hequiv3, Hequiv4.
  Qed.
End VM.

Global Arguments VM {_ _} _.
Global Arguments die {_ _ _}.
Global Arguments p_yield {_ _ _}.
Global Arguments p_io {_ _ _}.
Global Arguments p_spawn {_ _ _ _}.
Global Arguments initVm {_ _} _ {_}.

Section commut.
  Context `{IOH : IOHandler} {mbt1 mbt2 : Set} {pid1 pid2 : Ref}
    (Hpids : pid1 <> pid2).

  Let Program := @Program (h_request_t IOH) (h_reply_t IOH).

  Lemma yield_yield_commute cont1 cont2 :
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := @p_yield _ _ mbt1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := @p_yield _ _ mbt2 cont2 |}.
  Proof.
    apply vm_exec_commute.
    - sauto.
    - simpl. unfold schedule_in. apply pure_commutativity.
      sauto.
  Qed.

  Lemma die_die_commute :
    commute (h_terminate pid1) (h_terminate pid2) ->
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := die |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := die |}.
  Proof.
    intros Htermcomm.
    apply vm_exec_commute.
    - sauto.
    - unfold exec_proc, vm_process_die.
      now apply lift_w_commute.
  Qed.

  Lemma yield_die_commute cont1 :
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := @p_yield _ _ mbt1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := die |}.
  Proof.
    apply vm_exec_commute.
    - sauto.
    - unfold exec_proc, vm_process_die, schedule_in.
      intros vm1 vm3; split; intros H.
  Abort.

  Lemma io_io_commute req1 req2 cont1 cont2 :
    MFunRet_commute (h_handler pid1 req1) (h_handler pid2 req2) ->
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := p_io req1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := p_io req2 cont2 |}.
  Proof.
    intros Hcomm.
    apply vm_exec_commute.
    - sauto.
    - simpl. unfold vm_process_io.
      intros vm1 vm5; split; intros [vm3 [Hvm3 Hvm5]];
        destruct Hvm3 as [[ret2 vm2] [Hvm2 Hvm3]];
        destruct Hvm5 as [[ret4 vm4] [Hvm4 Hvm5]];
        simpl in Hvm3; simpl in Hvm5; subst;
        destruct vm1 as [w1 rq1 rc1];
        destruct vm2 as [w2 rq2 rc2];
        destruct vm4 as [w4 rq4 rc4];
        destruct Hvm2 as [Hw2 [Hrq2 Hrc2]];
        destruct Hvm4 as [Hw4 [Hrq4 Hrc4]];
        subst;
        [ destruct (Hcomm w1 w2 w4 ret2 ret4) as [Hcomm21 Hcomm12]
        | destruct (Hcomm w1 w2 w4 ret4 ret2) as [Hcomm21 Hcomm12]
        ];
        simpl in Hcomm12; simpl in Hcomm21.
      + apply Hcomm21 in Hw4. destruct Hw4 as [w4' [Hw2' Hequiv]].
        clear Hcomm12. clear Hcomm21.
        destruct Hw2' as [w2' [Hw2' Hw4']].
        exists {|
            world := w4';
            runq := {| pid := pid1; proc_mb_t := mbt1; cont := cont1 ret2 |} ::
                    {| pid := pid2; proc_mb_t := mbt2; cont := cont2 ret4 |} ::
                    rq2;
            ref_ctr := rc2
          |}.
        split.
        * apply mfun_assoc.
          exists (ret4, {| world := w2'; runq := rq2; ref_ctr := rc2 |}).
          split; [sauto|].
          exists {|
              world := w2';
              runq := {| pid := pid2; proc_mb_t := mbt2; cont := cont2 ret4 |} :: rq2;
              ref_ctr := rc2
            |}.
          split; [sauto|].
          exists (ret2,
              {|
              world := w4';
              runq := {| pid := pid2; proc_mb_t := mbt2; cont := cont2 ret4 |} :: rq2;
              ref_ctr := rc2
              |}).
          sauto.
        * sauto.
        * assumption.
      + apply Hcomm12 in Hw4. destruct Hw4 as [w4' [Hw2' Hequiv]].
        clear Hcomm12. clear Hcomm21.
        destruct Hw2' as [w2' [Hw2' Hw4']].
        exists {|
            world := w4';
            runq := {| pid := pid2; proc_mb_t := mbt2; cont := cont2 ret2 |} ::
                    {| pid := pid1; proc_mb_t := mbt1; cont := cont1 ret4 |} :: rq2;
            ref_ctr := rc2
          |}.
        split.
        * apply mfun_assoc.
          exists (ret4, {| world := w2'; runq := rq2; ref_ctr := rc2 |}).
          split; [sauto|].
          exists {|
              world := w2';
              runq := {| pid := pid1; proc_mb_t := mbt1; cont := cont1 ret4 |} :: rq2;
              ref_ctr := rc2
            |}.
          split; [sauto|].
          exists (ret2,
              {|
              world := w4';
              runq := {| pid := pid1; proc_mb_t := mbt1; cont := cont1 ret4 |} :: rq2;
              ref_ctr := rc2
              |}).
          sauto.
        * sauto.
        * assumption.
  Qed.

  Lemma spawn_spawn_commute {child_mb_t1 child_mb_t2 : Set}
    (child1 : Program child_mb_t1)
    (child2 : Program child_mb_t2) cont1 cont2 :
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := p_spawn child1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := p_spawn child2 cont2 |}.
  Proof.
    apply vm_exec_commute; [sauto|].
    intros vm1 vm5; split; simpl;
      intros [vm3 [Hvm3 Hvm5]];
      unfold process_spawn_morph, do_spawn in *;
      remember (make_ref pid1 vm1) as make_ref1;
      destruct make_ref1 as [child_pid1 vm2];
      remember (make_ref pid2 vm3) as make_ref2;
      destruct make_ref2 as [child_pid2 vm4].
    - subst.
      simpl in Heqmake_ref2.
  Abort.
End commut.

From Ltac2 Require
  Fresh
  String
  Ident
  Std.
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

(* Ltac2 step_vm_morph (hyp_id : Ident.t) := *)
(*   let hyp := Control.hyp hyp_id in *)
(*   lazy_match! Constr.type hyp with *)
(*   | vm_state_trans_morph ?vm (Some (?proc, ?vm')) => *)
(*       let (h_proc, h_pick, rq) *)
(*         := match Constr.Unsafe.kind proc with *)
(*            | Constr.Unsafe.Var h_proc_id => *)
(*                let h_proc_id := Ident.to_string h_proc_id in *)
(*                ( fresh_id (String.app "H_exec_" h_proc_id), *)
(*                  fresh_id (String.app "H_pick_" h_proc_id), *)
(*                  fresh_id (String.app "rq_wo_" h_proc_id) *)
(*                ) *)
(*            | _ => *)
(*                ( fresh_id "H_exec", *)
(*                  fresh_id "H_pick", *)
(*                  fresh_id "rq_" *)
(*                ) *)
(*            end in *)
(*       unfold_vm_hyp vm; *)
(*       unfold_vm_hyp vm'; *)
(*       unfold_proc_hyp proc; *)
(*       inversion_clear $hyp as [|? ? ? $rq ? ? $h_pick $h_proc] *)
(*   end. *)

(* Section tests. *)
(*   Context `{HIOh : IOHandler}. *)
(*   Goal forall vm1 vm2 proc, *)
(*       vm_state_trans_morph vm1 (Some (proc, vm2)) -> *)
(*       False. *)
(*     intros. *)
(*     step_vm_morph @H. *)
(*     match! goal with *)
(*     | [ h1 : Pick _ ?proc _, h2 : _ ~[exec_proc ?proc]~> _ |- _ ] => *)
(*         () *)
(*     end. *)
(*   Abort. *)
(* End tests. *)

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
  Abort.
End test.
