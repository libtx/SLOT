From Coq Require Import
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
  Mailbox.

From LibTx Require Import
  Storage
  Storage.Properties.

Import Setoids TransitionSystem ListSelector Mailbox Ref.FMap.
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

  Definition process_die_morph pid vm vm' :=
    vm' = vm <| world := h_terminate pid (world vm) |>.

  Lemma process_die_morph_covariance pid vm1 vm1' vm2 :
        vm1 == vm1' ->
        process_die_morph pid vm1 vm2 ->
        exists{vm2' == vm2}, process_die_morph pid vm1' vm2'.
  Proof.
    unfold process_die_morph, equiv, vm_setoid.
    destruct vm1, vm1'.
    intros Hvm1 Hvm2.
    subst.
    destruct Hvm1 as [Hw1 [Hc1 Hrq1]].
    apply h_terminate_covariance with (pid := pid) in Hw1.
    sauto.
  Qed.

  Definition process_yield_morph pid mb_t next vm vm' :=
    let proc := {| pid := pid; proc_mb_t := mb_t; cont := next |} in
    vm' = vm <| runq := proc :: (runq vm) |>.

  Lemma process_yield_morph_covariance pid mb_t next vm1 vm1' vm2 :
    vm1 == vm1' ->
    process_yield_morph pid mb_t next vm1 vm2 ->
    exists{vm2' == vm2}, process_yield_morph pid mb_t next vm1' vm2'.
  Proof.
    unfold process_yield_morph, equiv, vm_setoid.
    destruct vm1 as [w1 rq1 rc1].
    destruct vm1' as [w1' rq1' rc1'].
    destruct vm2 as [w2 rq2 rc2].
    intros Hvm1 Hvm2.
    sauto.
  Qed.

  Definition process_io_morph pid mb_t req next vm vm' :=
    exists io_reply,
      match vm' with
        {| world := w'; runq := rq'; ref_ctr := rc' |} =>
          let proc := {| pid := pid; proc_mb_t := mb_t; cont := next io_reply |} in
          morphism (h_handler pid req) (world vm) (io_reply, w') /\
            rq' = proc :: (runq vm) /\
            rc' = ref_ctr vm
      end.

  Lemma process_io_morph_covariance pid mb_t req next vm1 vm1' vm2 :
    vm1 == vm1' ->
    process_io_morph pid mb_t req next vm1 vm2 ->
    exists{vm2' == vm2}, process_io_morph pid mb_t req next vm1' vm2'.
  Proof.
    unfold process_io_morph, equiv, vm_setoid.
    destruct vm1 as [w1 rq1 rc1].
    destruct vm1' as [w1' rq1' rc1'].
    destruct vm2 as [w2 rq2 rc2].
    intros [Hw1 [Hrc1 Hrq1]].
    intros [reply [Hw2 [Hrq' Hrc']]]. simpl in Hw2.
    apply morphism_covariance with (x' := w1') in Hw2; [|assumption].
    destruct Hw2 as [[reply' w2'] [Hio [Hrep' Hw2']]].
    exists {| world := w2'; runq := {| pid := pid; proc_mb_t := mb_t; cont := next reply' |} :: rq1'; ref_ctr := rc1' |}.
    sauto.
  Qed.

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
    }.
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

  Definition exec_proc (proc : Process) (vm vm' : VM) : Prop :=
    match proc with
      {| pid := pid; proc_mb_t := mb_t; cont := prog |} =>
        match prog with
        | die _ =>
            process_die_morph pid vm vm'
        | p_yield _ next =>
            process_yield_morph pid mb_t next vm vm'
        | p_io _ req next =>
            process_io_morph pid mb_t req next vm vm'
        | @p_spawn _ child_mb_t child_prog next =>
            process_spawn_morph pid mb_t child_mb_t child_prog next vm vm'
        end
    end.

  Lemma exec_proc_covariance (proc : Process) vm1 vm1' vm2 :
    vm1 == vm1' ->
    exec_proc proc vm1 vm2 ->
    exists{vm2' == vm2}, exec_proc proc vm1' vm2'.
  Proof with eauto.
    unfold exec_proc.
    intros Hvm1 Hvm2.
    destruct proc as [pid mb_t cont].
    destruct cont.
    - eapply process_die_morph_covariance...
    - eapply process_yield_morph_covariance...
    - eapply process_io_morph_covariance...
    - eapply process_spawn_morph_covariance...
  Qed.

  Inductive vm_state_trans_morph : VM -> @ts_ret VM Process -> Prop :=
  | vm_state_trans_morph_none : forall w rc,
      vm_state_trans_morph
        {| world := w; ref_ctr := rc; runq := [] |}
        None
  | vm_state_trans_morph_some : forall w rc rq1 rq2 proc vm3,
      Pick rq1 proc rq2 ->
      exec_proc proc {| world := w; runq := rq2; ref_ctr := rc |} vm3 ->
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
      apply exec_proc_covariance with (vm1' := {| world := w1'; runq := rq2'; ref_ctr := rc1'|}) in Hvm3; [|sauto].
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

  Lemma yield_yield_commut pid1 pid2 mbt1 mbt2 cont1 cont2 :
    pid1 <> pid2 ->
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := @p_yield mbt1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := @p_yield mbt2 cont2 |}.
  Proof.
    intros Hpids vm1 vm1'.
    destruct vm1 as [w1 rq1 rc1]. destruct vm1' as [w1' rq1' rc1'].
    simpl. split; intros H.
    - destruct H as [vm2 [Hvm2 Hvm3]].
      inversion_clear Hvm2.
      destruct vm2 as [w2 rq2_ rc2].
      inversion_clear Hvm3. simpl in *. unfold process_yield_morph in *. simpl in *.
  Abort.

  Lemma spawn_spawn_commut pid1 pid2 mbt1 mbt2 mbt1' mbt2' child1 child2 cont1 cont2 :
    pid1 <> pid2 ->
    event_commute {| pid := pid1; proc_mb_t := mbt1; cont := @p_spawn mbt1 mbt1' child1 cont1 |}
                  {| pid := pid2; proc_mb_t := mbt2; cont := @p_spawn mbt2 mbt2' child2 cont2 |}.
  Proof.
    intros Hpids vm1 vm1'.
    destruct vm1 as [w1 rq1 rc1]. destruct vm1' as [w1' rq1' rc1'].
  Abort.
End VM.

Global Arguments VM {_ _} _.
Global Arguments die {_ _ _}.
Global Arguments p_yield {_ _ _}.
Global Arguments p_io {_ _ _}.
Global Arguments p_spawn {_ _ _ _}.
Global Arguments initVm {_ _} _ {_}.

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
    - exfalso. inversion_clear H.
    - simpl in H0.
  Abort.
End test.
