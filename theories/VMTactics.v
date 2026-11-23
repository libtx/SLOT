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

(** * Stepping tactics for the VM transition system

    This module provides reusable Ltac2 tactics for "stepping" through
    the states of the [TransitionSystem] instantiated with the VM
    ([vmTransitionSystem]).

    The tactics follow three rules:

    - every tactic consumes ONE hypothesis whose shape is matched
      syntactically (up to a small, fixed normalization step);

    - all reasoning is performed by a set of "canned" inversion lemmas
      proved below (no proof search);

    - the results of the decomposition are returned as Ltac2 algebraic
      data ([vm_step_res], [vm_exec_res], [pick_cons_res]) whose
      constructors carry records with named fields, so that composed
      tactics never have to guess the meaning of a positional
      argument.

    All tactics take a name prefix explicitly (conventionally the name
    of the hypothesis' source state); all generated names are derived
    from it mechanically.

    Given a transition hypothesis

      [H : vm0 ~[ts_mfun tr]~> vm2]                (one transition, or
      [H : TSMFunGen vm0 trace vm2]                 one trace layer)

    [vm_step vm0 H] decomposes one transition into:

      [vm0_w, vm0_rq, vm0_rc]                       (state components)
      [vm2_w, vm2_rq, vm2_rc]
      [vm0_rest]                                    (runq after pick)
      [Hvm0_pick : Pick vm0_rq (tr_proc tr) vm0_rest]
      [Hvm0_exec : exec_proc_morph ...]             (see [vm_exec])

    and [vm_exec vm0 Hvm0_exec] further decomposes the execution step
    of the scheduled-out process, according to its (concrete)
    continuation: [exit], [p_io], [p_spawn] or [p_halt].

    For multi-transition traces, [vm_run_trace vm0 H] walks the whole
    trace, prefixing the steps with [vm0], [vm0_mid],
    [vm0_mid_mid], ...; [vm_destruct vm1 vm2 ...] destructs VM states
    into their components.

    The [Pick] hypotheses produced by stepping are analyzed with
    [pick_case p H] (goal-splitting case analysis: the element is at
    the head of the list or in the tail) and [pick_cons p H Hne]
    (peels a head known to differ from the picked element, returning
    the new names as a tuple for further threading).
*)

From Stdlib Require Import
  List.

Import ListNotations.

From SLOT Require Import
  TransitionSystem
  VM
  ListSelector
  Tactics.

Open Scope slot_scope.

(* The lemma sections below are written in Ltac1 ("Classic", the
   default proof mode), regardless of the proof mode set by the
   imported modules. *)
Set Default Proof Mode "Classic".

(** ** Canned inversion lemmas: generic transition systems *)

Section TSSteppingLemmas.
  Context {State Event : Type} `{Hts : @TransitionSystem State Event}.

  (** A trace of length zero does not move and the system is stuck. *)
  Lemma ts_mfun_gen_nil_inv (s s' : State) :
    TSMFunGen s [] s' ->
    s ~[ts_state_trans]~> None /\ s = s'.
  Proof.
    intros H.
    inversion_clear H.
    split; [assumption | now subst].
  Qed.

  (** A nonempty trace steps with the head event. *)
  Lemma ts_mfun_gen_cons_inv (s : State) (event : Event) (t : list Event)
      (s' : State) :
    TSMFunGen s (event :: t) s' ->
    exists smid,
      s ~[ts_state_trans]~> Some (event, smid) /\
      TSMFunGen smid t s'.
  Proof.
    intros H.
    inversion_clear H.
    eexists.
    split; eassumption.
  Qed.
End TSSteppingLemmas.

(** ** Canned inversion lemmas: picking from lists *)

Section PickLemmas.
  Context {A : Type}.

  (** Nothing can be picked from an empty list. *)
  Lemma pick_nil_absurd (a : A) (l' : list A) :
    Pick [] a l' -> False.
  Proof.
    intros H.
    unfold Pick in H.
    inversion H.
  Qed.

  (** Full case analysis on [Pick]: the picked element is either at
      the head of the list, or somewhere in the tail (in which case
      the heads of the two lists coincide). *)
  Lemma pick_case_inv (a : A) (l l' : list A) :
    Pick l a l' ->
    (exists tl, l = a :: tl /\ l' = tl) \/
    (exists hd tl l'', l = hd :: tl /\ l' = hd :: l'' /\ Pick tl a l'').
  Proof.
    intros H.
    destruct l as [|hd tl].
    - exfalso. exact (pick_nil_absurd a l' H).
    - unfold Pick in H.
      inversion_clear H.
      + left. subst. eexists. split; reflexivity.
      + right. subst. exists hd, tl. eexists.
        split; [reflexivity |].
        split; [reflexivity |].
        unfold Pick. eassumption.
  Qed.
End PickLemmas.

(** ** Canned inversion lemmas: the VM *)

Section VMSteppingLemmas.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler_basics Request Reply}.

  (** A VM with an empty run queue is stuck. *)
  Lemma vm_step_none_inv w rq rc :
    vm_step_morph {| world := w; runq := rq; ref_ctr := rc |} None ->
    rq = [].
  Proof.
    intros H.
    inversion_clear H.
    match goal with
    | [ Hs : _ ~[schedule_out]~> None |- _ ] =>
        destruct rq as [|p rest];
          [ reflexivity
          | unfold schedule_out in Hs; cbn in Hs; contradiction ]
    end.
  Qed.

  (** One transition = one scheduling step + one execution step. *)
  Lemma vm_step_some_inv w rq rc tr vm2 :
    vm_step_morph {| world := w; runq := rq; ref_ctr := rc |} (Some (tr, vm2)) ->
    exists vm1,
      {| world := w; runq := rq; ref_ctr := rc |} ~[schedule_out]~>
        Some (tr_proc tr, vm1) /\
      exec_proc_morph (tr_proc tr) vm1 (tr, vm2).
  Proof.
    intros H.
    inversion_clear H.
    eexists.
    split; eassumption.
  Qed.

  (** Scheduling out only touches the run queue. *)
  Lemma schedule_out_inv w1 rq1 rc1 proc w2 rq2 rc2 :
    {| world := w1; runq := rq1; ref_ctr := rc1 |} ~[schedule_out]~>
      Some (proc, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    Pick rq1 proc rq2 /\ w1 = w2 /\ rc1 = rc2.
  Proof.
    intros H.
    unfold schedule_out in H.
    cbn in H.
    destruct rq1 as [|p rest].
    - discriminate H.
    - exact H.
  Qed.

  (** Execution step: [exit]. *)
  Lemma terminate_inv proc w1 rq1 rc1 tr w2 rq2 rc2 :
    {| world := w1; runq := rq1; ref_ctr := rc1 |} ~[terminate proc]~>
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    w1 ~[h_terminate true (pid proc)]~> w2 /\ rq2 = rq1 /\ rc2 = rc1 /\
      tr = terminate_tr proc.
  Proof.
    intros H.
    unfold terminate, terminate_morph, lift_w in H.
    cbn in H.
    destruct H as [[Hw [Hrq Hrc]] Htr].
    repeat split.
    - exact Hw.
    - symmetry; exact Hrq.
    - symmetry; exact Hrc.
    - exact Htr.
  Qed.

  (** Execution step: [p_io]. *)
  Lemma perform_io_inv proc req cnt w1 rq1 rc1 tr w2 rq2 rc2 :
    {| world := w1; runq := rq1; ref_ctr := rc1 |}
      ~[perform_io proc req cnt]~>
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    exists rep : Reply req,
      w1 ~[h_perform_io (pid proc) req]~> (rep, w2) /\
        tr = perform_io_tr proc req cnt rep /\
        rc2 = rc1 /\
        rq2 = {| pid := pid proc; proc_mb_t := proc_mb_t proc;
                 cont := cnt rep |} :: rq1.
  Proof.
    intros H.
    unfold perform_io, perform_io_morph in H.
    cbn in H.
    exact H.
  Qed.

  (** Execution step: [p_spawn]. *)
  Lemma spawn_inv parent child_mb_t child_cont parent_cont
      w1 rq1 rc1 tr w2 rq2 rc2 :
    {| world := w1; runq := rq1; ref_ctr := rc1 |}
      ~[VM.spawn parent child_mb_t child_cont parent_cont]~>
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    exists new_pid rc',
      Fresh.make (pid parent) rc1 = (new_pid, rc') /\
      w1 ~[h_spawn new_pid child_mb_t]~> w2 /\
      tr = spawn_tr parent child_mb_t child_cont parent_cont new_pid /\
      rq2 = {| pid := pid parent; proc_mb_t := proc_mb_t parent;
               cont := parent_cont (mkAddress child_mb_t new_pid) |}
           :: {| pid := new_pid; proc_mb_t := child_mb_t;
                 cont := child_cont |}
           :: rq1 /\
      rc2 = rc'.
  Proof.
    intros H.
    destruct (Fresh.make (pid parent) rc1) as [new_pid rc'] eqn:Hfresh.
    unfold VM.spawn, spawn_morph, alloc_pid in H.
    cbn in H.
    rewrite Hfresh in H.
    cbn in H.
    destruct H as [w2' Hstep Hconj].
    destruct Hconj as [Htr Hvm].
    injection Hvm as Hw2 Hrq2 Hrc2.
    subst.
    exists new_pid.
    exists rc'.
    repeat split; try reflexivity.
    exact Hstep.
  Qed.

  (** The same three steps, stated over [exec_proc_morph] with a
      concrete process, so that the continuation is selected by
      unification when the tactic applies the lemma. *)

  Lemma exec_exit_inv pid1 mb1 w1 rq1 rc1 tr w2 rq2 rc2 :
    exec_proc_morph {| pid := pid1; proc_mb_t := mb1; cont := exit |}
      {| world := w1; runq := rq1; ref_ctr := rc1 |}
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    w1 ~[h_terminate true pid1]~> w2 /\ rq2 = rq1 /\ rc2 = rc1 /\
      tr = terminate_tr {| pid := pid1; proc_mb_t := mb1; cont := exit |}.
  Proof.
    intros H.
    exact (terminate_inv _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma exec_io_inv (pid1 : Pid) (mb1 : Set) (req : Request)
      (cnt : Reply req -> Program mb1) w1 rq1 rc1 tr w2 rq2 rc2 :
    exec_proc_morph {| pid := pid1; proc_mb_t := mb1; cont := p_io req cnt |}
      {| world := w1; runq := rq1; ref_ctr := rc1 |}
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    exists rep : Reply req,
      w1 ~[h_perform_io pid1 req]~> (rep, w2) /\
        tr = perform_io_tr
          {| pid := pid1; proc_mb_t := mb1; cont := p_io req cnt |} req cnt rep /\
        rc2 = rc1 /\
        rq2 = {| pid := pid1; proc_mb_t := mb1; cont := cnt rep |} :: rq1.
  Proof.
    intros H.
    exact (perform_io_inv _ _ _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma exec_spawn_inv (pid1 : Pid) (mb1 mb2 : Set)
      (child : Program mb2) (pc : @Address mb2 -> Program mb1)
      w1 rq1 rc1 tr w2 rq2 rc2 :
    exec_proc_morph {| pid := pid1; proc_mb_t := mb1; cont := p_spawn child pc |}
      {| world := w1; runq := rq1; ref_ctr := rc1 |}
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    exists new_pid rc',
      Fresh.make pid1 rc1 = (new_pid, rc') /\
      w1 ~[h_spawn new_pid mb2]~> w2 /\
      tr = spawn_tr {| pid := pid1; proc_mb_t := mb1;
                       cont := p_spawn child pc |} mb2 child pc new_pid /\
      rq2 = {| pid := pid1; proc_mb_t := mb1;
               cont := pc (mkAddress mb2 new_pid) |}
           :: {| pid := new_pid; proc_mb_t := mb2; cont := child |}
           :: rq1 /\
      rc2 = rc'.
  Proof.
    intros H.
    exact (spawn_inv _ _ _ _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma exec_halt_inv (pid1 : Pid) (mb1 : Set)
      (node : Corelib.Numbers.BinNums.positive)
      w1 rq1 rc1 tr w2 rq2 rc2 :
    exec_proc_morph {| pid := pid1; proc_mb_t := mb1; cont := p_halt mb1 node |}
      {| world := w1; runq := rq1; ref_ctr := rc1 |}
      (tr, {| world := w2; runq := rq2; ref_ctr := rc2 |}) ->
    False.
  Proof.
    intros H.
    exact H.
  Qed.
End VMSteppingLemmas.

(** ** Ltac2 stepping tactics *)

From Ltac2 Require
  Fresh
  String
  Message
  Ident
  Std
  Constr
  Control.
From Ltac2 Require Import
  Notations
  Printf
  Init
  RedFlags.

Set Default Proof Mode "Ltac2".

(** Payload of [VmStepSome]: [prefix] is the name prefix used for
    the generated hypotheses, [pick] is [H<prefix>_pick : Pick ...],
    [rest] is the run queue variable [<prefix>_rest] left after the
    process was scheduled out, and [exec] is [H<prefix>_exec] (see
    [vm_exec]). *)
Ltac2 Type vm_step_some := {
  prefix : string;
  pick : ident;
  rest : ident;
  exec : ident;
}.

(** Result of decomposing one transition of the VM transition system:

    - [VmStepNone stuck]: the system is stuck, [stuck] is the
      hypothesis [runq vm = []];

    - [VmStepSome info]: one transition was decomposed; the record
      fields are [prefix] (the name prefix used for the generated
      hypotheses), [pick] ([H<prefix>_pick : Pick ...]), [rest] (the
      run queue variable [<prefix>_rest] left after the process was
      scheduled out) and [exec] ([H<prefix>_exec], see [vm_exec]);

    - [VmStepTrace info]: a [TSMFunGen] layer was peeled off; the
      record fields are [trace] ([H<prefix>_trace] for the rest of
      the trace) and [step] (the transition itself). *)
Ltac2 Type rec vm_step_res := [
  VmStepNone (ident)
| VmStepSome (vm_step_some)
| VmStepTrace (vm_step_trace)
] with vm_step_trace := {
  trace : ident;
  step : vm_step_res;
}.

(** Shared payload of the terminating execution steps: [w] is the
    world-step hypothesis [H<p>_w], [tr] is the trace-equation
    hypothesis [H<p>_tr]. *)
Ltac2 Type vm_exec_tail := {
  w : ident;
  tr : ident;
}.

(** Payload of [VmExecPerformIO]: [rep] is the reply variable
    [<p>_rep]. *)
Ltac2 Type vm_exec_io := {
  rep : ident;
  io_tail : vm_exec_tail;
}.

(** Payload of [VmExecSpawn]: [new_pid] and [new_rc] are the freshly
    allocated pid and ref counter ([<p>_new_pid], [<p>_new_rc]),
    [fresh] is [H<p>_fresh : Fresh.make ... = (new_pid, new_rc)]. *)
Ltac2 Type vm_exec_spawn := {
  new_pid : ident;
  new_rc : ident;
  fresh : ident;
  spawn_tail : vm_exec_tail;
}.

(** Result of decomposing one execution step ([vm_exec]):

    - [VmExecTerminate info]: see [vm_exec_tail];

    - [VmExecPerformIO info]: see [vm_exec_io];

    - [VmExecSpawn info]: see [vm_exec_spawn];

    - [VmExecHalt]: the hypothesis is [False] ([H<p>_halt]). *)
Ltac2 Type vm_exec_res := [
  VmExecTerminate (vm_exec_tail)
| VmExecPerformIO (vm_exec_io)
| VmExecSpawn (vm_exec_spawn)
| VmExecHalt
].

Ltac2 vm_ctl_fail (msg : string) : 'a :=
  Control.zero (Tactic_failure (Some (Message.of_string msg))).

Ltac2 vm_hyp_name (p : string) (suffix : string) : string :=
  String.app (String.app "H" p) suffix.

(** Destruct a VM state into its [world], [runq] and [ref_ctr]
    components, named [<name>_w], [<name>_rq], [<name>_rc].  Does
    nothing when [vm] is not a context variable. *)
Ltac2 vm_destruct_constr (vm : constr) : unit :=
  match Constr.Unsafe.kind vm with
  | Constr.Unsafe.Var v =>
      let name := Ident.to_string v in
      let w := fresh_id (String.app name "_w") in
      let rq := fresh_id (String.app name "_rq") in
      let rc := fresh_id (String.app name "_rc") in
      let hvm := Control.hyp v in
      destruct $hvm as [$w $rq $rc]
  | _ => ()
  end.

Ltac2 vm_destruct (vms : ident list) : unit :=
  List.iter
    (fun id =>
       let hvm := Control.hyp id in
       match! Constr.type hvm with
       | VM => vm_destruct_constr hvm
       | _ =>
           vm_ctl_fail (String.app "vm_destruct: not a VM state: "
                          (Ident.to_string id))
       end)
    vms.

Ltac2 Notation "vm_destruct" ids(list0(ident)) := vm_destruct ids.

(** If the LHS of the equation hypothesis [h] is a context variable,
    substitute it away; otherwise keep the equation under its name. *)
Ltac2 vm_elim_eq (h : ident) : unit :=
  match! Constr.type (Control.hyp h) with
  | ?end_term = _ =>
      match Constr.Unsafe.kind end_term with
      | Constr.Unsafe.Var v => subst $v
      | _ => ()
      end
  | _ => ()
  end.

(** Decompose one execution step of the scheduled-out process.  The
    continuation of the process must be a concrete constructor
    ([exit], [p_io], [p_spawn] or [p_halt]); it is selected by
    unification when the canned [exec_*_inv] lemma is applied.

    Returns [None] when the hypothesis is not an [exec_proc_morph]
    with a concrete continuation (e.g. the event is still a variable
    during trace stepping). *)
Ltac2 vm_exec_opt (p : string) (id : ident) : vm_exec_res option :=
  let hyp := Control.hyp id in
  match! Constr.type hyp with
  | exec_proc_morph _ _ (_, _) =>
      try (apply exec_exit_inv in $id);
      try (apply exec_io_inv in $id);
      try (apply exec_spawn_inv in $id);
      try (apply exec_halt_inv in $id);
      let hw := fresh_id (vm_hyp_name p "_w") in
      let htr := fresh_id (vm_hyp_name p "_tr") in
      let hrq := fresh_id (vm_hyp_name p "_rq") in
      let hrc := fresh_id (vm_hyp_name p "_rc") in
      let hd := Control.hyp id in
      lazy_match! Constr.type hd with
      | _ ~[h_terminate _ _]~> _ /\ _ /\ _ /\ _ =>
          destruct $hd as [$hw [$hrq [$hrc $htr]]];
          vm_elim_eq hrq;
          vm_elim_eq hrc;
          Some (VmExecTerminate { w := hw; tr := htr })
      | context [h_perform_io _ _] =>
          let hrep := fresh_id (String.app p "_rep") in
          destruct $hd as [$hrep [$hw [$htr [$hrc $hrq]]]];
          vm_elim_eq hrc;
          vm_elim_eq hrq;
          Some (VmExecPerformIO
                  { rep := hrep; io_tail := { w := hw; tr := htr } })
      | context [Fresh.make _ _] =>
          let hnp := fresh_id (String.app p "_new_pid") in
          let hnc := fresh_id (String.app p "_new_rc") in
          let hfresh := fresh_id (vm_hyp_name p "_fresh") in
          destruct $hd as [$hnp [$hnc [$hfresh [$hw [$htr [$hrq $hrc]]]]]];
          vm_elim_eq hrq;
          vm_elim_eq hrc;
          Some (VmExecSpawn
                  { new_pid := hnp; new_rc := hnc; fresh := hfresh;
                    spawn_tail := { w := hw; tr := htr } })
      | False =>
          Std.rename [(id, fresh_id (vm_hyp_name p "_halt"))];
          Some VmExecHalt
      | _ => None
      end
  | _ => None
  end.

(** Strict version of [vm_exec_opt]: fails with an error message when
    the execution step cannot be decomposed. *)
Ltac2 vm_exec (p : string) (id : ident) : vm_exec_res :=
  match vm_exec_opt p id with
  | Some r => r
  | None =>
      vm_ctl_fail (String.app
                     (String.app "vm_exec: cannot decompose "
                        (Ident.to_string id))
                     " (is the process continuation concrete?)")
  end.

(** Decompose ONE step of the VM transition system, in any of the
    shapes produced by [ts_mfun], [ts_state_trans] or [TSMFunGen]
    (with a concrete trace constructor).  [p] is the prefix for the
    names of the generated hypotheses (conventionally the name of the
    hypothesis' source state).  See [vm_step_res] for the naming
    convention. *)
Ltac2 rec vm_step (p : string) (id : ident) : vm_step_res :=
  let hyp := Control.hyp id in
  (* Normalize the TransitionSystem-level wrappers down to
     [vm_step_morph], as a pure constr computation (the hypothesis
     itself is not modified; the canned lemmas are applied to it by
     conversion). *)
  let ty :=
    Std.eval_lazy
      red_flags:(beta iota zeta delta
                   [ts_mfun morphism ts_state_trans vm_step vmTransitionSystem])
      (Constr.type hyp) in
  lazy_match! ty with
  (* ----- one transition: the system is stuck ----- *)
  | vm_step_morph ?vm0 None =>
      let hstuck := fresh_id (vm_hyp_name p "_stuck") in
      vm_destruct_constr vm0;
      apply vm_step_none_inv in $id as $hstuck;
      Std.clear [id];
      VmStepNone hstuck
  (* ----- one transition: schedule out + execute ----- *)
  | vm_step_morph ?vm0 (Some (_, ?vm2)) =>
      let hout := fresh_id (String.app p "_out") in
      let hsched := fresh_id (vm_hyp_name p "_sched") in
      let hexec := fresh_id (vm_hyp_name p "_exec") in
      vm_destruct_constr vm0;
      vm_destruct_constr vm2;
      destruct (vm_step_some_inv _ _ _ _ _ $hyp) as [$hout [$hsched $hexec]];
      (* Decompose the intermediate (scheduled-out) state: only the
         run queue survives under a new name. *)
      let wtmp := fresh_id "w" in
      let hrest := fresh_id (String.app p "_rest") in
      let rctmp := fresh_id "rc" in
      let hout_c := Control.hyp hout in
      destruct $hout_c as [$wtmp $hrest $rctmp];
      let hsched_c := Control.hyp hsched in
      let hpick := fresh_id (vm_hyp_name p "_pick") in
      let hweq := fresh_id (vm_hyp_name p "_w_eq") in
      let hrceq := fresh_id (vm_hyp_name p "_rc_eq") in
      destruct (schedule_out_inv _ _ _ _ _ _ _ $hsched_c)
        as [$hpick [$hweq $hrceq]];
      subst $wtmp;
      subst $rctmp;
      Std.clear [hsched; id];
      VmStepSome { prefix := p; pick := hpick; rest := hrest; exec := hexec }
  (* ----- one layer of a trace: step event, keep the rest ----- *)
  | TSMFunGen _ (_ :: _) _ =>
      let pmid := String.app p "_mid" in
      let hmid := fresh_id pmid in
      let hstep := fresh_id (vm_hyp_name p "_step") in
      let htrace := fresh_id (vm_hyp_name p "_trace") in
      destruct (ts_mfun_gen_cons_inv _ _ _ _ $hyp) as [$hmid [$hstep $htrace]];
      Std.clear [id];
      VmStepTrace { trace := htrace; step := vm_step p hstep }
  (* ----- an empty trace: the system is stuck ----- *)
  | TSMFunGen _ [] ?vm1 =>
      let hstep := fresh_id (vm_hyp_name p "_step") in
      let heq := fresh_id (vm_hyp_name p "_eq") in
      destruct (ts_mfun_gen_nil_inv _ _ $hyp) as [$hstep $heq];
      Std.clear [id];
      match Constr.Unsafe.kind vm1 with
      | Constr.Unsafe.Var v => subst $v
      | _ => ()
      end;
      vm_step p hstep
  | _ =>
      vm_ctl_fail "vm_step: hypothesis is not a VM transition step \
                   (a variable trace should be destructed first)"
  end.

(** Walk a whole [TSMFunGen] hypothesis through all the states of the
    transition system, decomposing every transition.  [p] is the name
    prefix for the first step (subsequent steps are prefixed with
    [<p>_mid], [<p>_mid_mid], ...).  The trace must be a concrete list;
    execution steps are left as [H<prefix>_exec] hypotheses
    (decompose them with [vm_exec]).  Returns the list of individual
    step results. *)
Ltac2 rec vm_run_trace (p : string) (id : ident) : vm_step_res list :=
  match vm_step p id with
  | VmStepTrace { trace := htrace; step := s } =>
      s :: vm_run_trace (String.app p "_mid") htrace
  | step => [step]
  end.

Ltac2 Notation "vm_step" p(ident) x(ident) :=
  let _ := vm_step (Ident.to_string p) x in ().
Ltac2 Notation "vm_exec" p(ident) x(ident) :=
  let _ := vm_exec (Ident.to_string p) x in ().
Ltac2 Notation "vm_run_trace" p(ident) x(ident) :=
  let _ := vm_run_trace (Ident.to_string p) x in ().

(** ** Case analysis on [Pick]

    [pick_case p H], where [H : Pick l a l'], splits the goal into two
    subgoals:

    - the element is at the head: [l] is substituted by [a :: l']
      (equation [H<p>_l_eq] if [l] is not a variable);

    - the element is in the tail: new variables [<p>_hd], [<p>_tl],
      [<p>_tl2] with [l] substituted by [<p>_hd :: <p>_tl], [l'] by
      [<p>_hd :: <p>_tl2], and the residual [Pick <p>_tl a <p>_tl2]
      renamed back to [H].

    When the source list is empty, [H] becomes [False].

    Like [destruct], this tactic splits the goal, so it returns
    [unit]; the per-branch results are addressed by their
    deterministic names above. *)
Ltac2 pick_case (p : string) (id : ident) : unit :=
  let hyp := Control.hyp id in
  match! Constr.type hyp with
  | Pick [] _ _ =>
      (* Nothing can be picked from an empty list. *)
      apply pick_nil_absurd in $id
  | Pick _ _ _ =>
      let htl := fresh_id (String.app p "_tl") in
      let hhd := fresh_id (String.app p "_hd") in
      let htl2 := fresh_id (String.app p "_tl2") in
      let hl_eq := fresh_id (vm_hyp_name p "_l_eq") in
      let hr_eq := fresh_id (vm_hyp_name p "_r_eq") in
      let hpick := fresh_id (vm_hyp_name p "_pick") in
      destruct (pick_case_inv _ _ _ $hyp)
        as [[$htl [$hl_eq $hr_eq]]
           | [$hhd [$htl [$htl2 [$hl_eq [$hr_eq $hpick]]]]]];
      Std.clear [id];
      Control.dispatch
        [ (fun () =>
             (* The element is at the head. *)
             subst $htl;
             vm_elim_eq hl_eq);
          (fun () =>
             (* The element is in the tail. *)
             vm_elim_eq hl_eq;
             vm_elim_eq hr_eq;
             Std.rename [(hpick, id)]) ]
  | _ =>
      vm_ctl_fail "pick_case: hypothesis is not a Pick"
  end.

Ltac2 Notation "pick_case" p(ident) x(ident) :=
  pick_case (Ident.to_string p) x.

(** Result of [pick_cons]: [rest2] is the new rest list variable
    [<p>_tl2] (the picked list's tail), [eq] is the hypothesis
    [H<p>_eq : l' = x :: <p>_tl2], and [residual] is the residual
    [Pick l a <p>_tl2] hypothesis (renamed back to the original
    name). *)
Ltac2 Type pick_cons_res := {
  rest2 : ident;
  eq : ident;
  residual : ident;
}.

(** Peel one element from the head of a [Pick] when it is known to
    differ from the picked element: given

      [H : Pick (x :: l) a l']   and   [Hne : x <> a],

    [pick_cons p H Hne] applies the canned [pick_cons] lemma WITHOUT
    splitting the goal, and returns a [pick_cons_res] record

      { rest2 := [<p>_tl2];        (* l' = x :: <p>_tl2 *)
        eq := [H<p>_eq];           (* the equation above *)
        residual := [H] }          (* residual: Pick l a <p>_tl2,
                                      renamed back to [H] *)

    so that tactic writers can thread the results without searching
    for names.  Nothing is substituted away; the caller remains in
    full control of the equations. *)
Ltac2 pick_cons (p : string) (id : ident) (hne : ident) : pick_cons_res :=
  let hyp := Control.hyp id in
  match! Constr.type hyp with
  | Pick (_ :: _) _ _ =>
      let htl2 := fresh_id (String.app p "_tl2") in
      let heq := fresh_id (vm_hyp_name p "_eq") in
      let hpick := fresh_id (vm_hyp_name p "_pick") in
      let hne_c := Control.hyp hne in
      destruct (pick_cons $hyp $hne_c) as [$htl2 [$heq $hpick]];
      Std.clear [id];
      Std.rename [(hpick, id)];
      { rest2 := htl2; eq := heq; residual := id }
  | _ =>
      vm_ctl_fail "pick_cons: hypothesis is not a Pick of a nonempty list"
  end.

Ltac2 Notation "pick_cons" p(ident) x(ident) hne(ident) :=
  let _ := pick_cons (Ident.to_string p) x hne in ().

(* begin hide *)
Section tests.
  Context {Request : Type} {Reply : Request -> Type}
          `{IOH : @IOHandler_basics Request Reply}.

  (* One I/O transition: the continuation of the process is put back
     at the head of the run queue. *)
  Goal forall (p : Pid) (mb : Set) (req : Request)
             (cnt : Reply req -> Program mb) (rep : Reply req)
             (vm0 vm2 : VM),
    vm0 ~[ts_mfun {| tr_proc := {| pid := p; proc_mb_t := mb;
                                   cont := p_io req cnt |};
                     tr_result := rep |}]~> vm2 ->
    exists rep' : Reply req,
      exists rest : list Process,
        runq vm2 = {| pid := p; proc_mb_t := mb; cont := cnt rep' |} :: rest.
  Proof.
    intros p mb req cnt rep vm0 vm2 H.
    vm_step vm0 H.
    vm_exec vm0 Hvm0_exec.
    cbn.
    exists vm0_rep.
    exists vm0_rest.
    reflexivity.
  Qed.

  (* One exit step in a trace. *)
  Goal forall (p : Pid) (mb : Set) (vm0 vm2 : VM),
    TSMFunGen vm0
      [ {| tr_proc := {| pid := p; proc_mb_t := mb; cont := exit |};
          tr_result := I |} ]
      vm2 ->
    exists rest : list Process,
      Pick (runq vm0) {| pid := p; proc_mb_t := mb; cont := exit |} rest /\
        runq vm2 = rest.
  Proof.
    intros p mb vm0 vm2 H.
    vm_step vm0 H.
    vm_step vm0_mid Hvm0_trace.
    vm_exec vm0 Hvm0_exec.
    cbn.
    exists vm0_rest.
    split.
    - exact Hvm0_pick.
    - reflexivity.
  Qed.

  (* A nonempty VM cannot step to [None]. *)
  Goal forall (vm : VM) (proc : Process) (rq : list Process),
    runq vm = proc :: rq ->
    vm ~[ts_state_trans]~> None ->
    False.
  Proof.
    intros vm proc rq Hrq H.
    vm_step vm H.
    cbn in Hrq.
    rewrite Hvm_stuck in Hrq.
    discriminate Hrq.
  Qed.

  (* One spawn transition. *)
  Goal forall (mb1 mb2 : Set) (p : Pid) (child : Program mb2)
             (pc : @Address mb2 -> Program mb1) (np : Pid)
             (vm0 vm2 : VM),
    vm0 ~[ts_mfun {| tr_proc := {| pid := p; proc_mb_t := mb1;
                                   cont := p_spawn child pc |};
                     tr_result := np |}]~> vm2 ->
    exists new_pid : Pid,
      exists rest : list Process,
        runq vm2 = {| pid := p; proc_mb_t := mb1;
                      cont := pc (mkAddress mb2 new_pid) |}
                   :: {| pid := new_pid; proc_mb_t := mb2; cont := child |}
                   :: rest.
  Proof.
    intros mb1 mb2 p child pc np vm0 vm2 H.
    vm_step vm0 H.
    vm_exec vm0 Hvm0_exec.
    cbn.
    exists vm0_new_pid.
    exists vm0_rest.
    reflexivity.
  Qed.

  (* Halting the VM makes the step hypothesis [False]. *)
  Goal forall (mb : Set) (p : Pid)
             (node : Corelib.Numbers.BinNums.positive)
             (vm0 vm2 : VM),
    vm0 ~[ts_mfun {| tr_proc := {| pid := p; proc_mb_t := mb;
                                   cont := p_halt mb node |};
                     tr_result := I |}]~> vm2 ->
    False.
  Proof.
    intros mb p node vm0 vm2 H.
    vm_step vm0 H.
    vm_exec vm0 Hvm0_exec.
    exact Hvm0_halt.
  Qed.

  (* Stepping through a two-transition trace. *)
  Goal forall (p : Pid) (mb : Set) (req : Request)
             (cnt : Reply req -> Program mb) (rep : Reply req)
             (vm0 vm2 : VM),
    TSMFunGen vm0
      [ {| tr_proc := {| pid := p; proc_mb_t := mb; cont := p_io req cnt |};
          tr_result := rep |};
        {| tr_proc := {| pid := p; proc_mb_t := mb; cont := exit |};
          tr_result := I |} ]
      vm2 ->
    exists (rep' : Reply req) (rest1 rest2 : list Process),
      Pick (runq vm0) {| pid := p; proc_mb_t := mb; cont := p_io req cnt |} rest1 /\
        Pick ({| pid := p; proc_mb_t := mb; cont := cnt rep' |} :: rest1)
             {| pid := p; proc_mb_t := mb; cont := exit |} rest2 /\
          runq vm2 = rest2.
  Proof.
    intros p mb req cnt rep vm0 vm2 H.
    vm_run_trace vm0 H.
    vm_exec vm0 Hvm0_exec.
    vm_exec vm0_mid Hvm0_mid_exec.
    cbn.
    exists vm0_rep.
    exists vm0_rest.
    exists vm0_mid_rest.
    split.
    - exact Hvm0_pick.
    - split.
      + exact Hvm0_mid_pick.
      + reflexivity.
  Qed.
  (* Case analysis on Pick: the element is at the head or in the tail. *)
  Goal forall (a : @Process Request Reply)
             (rq rest : list (@Process Request Reply)),
    Pick rq a rest ->
    rq = a :: rest \/
    exists hd tl rest2,
      rq = hd :: tl /\ rest = hd :: rest2 /\ Pick tl a rest2.
  Proof.
    intros a rq rest H.
    pick_case rq H.
    - left. reflexivity.
    - right. exists rq_hd, rq_tl, rq_tl2.
      split.
      + reflexivity.
      + split.
        * reflexivity.
        * exact H.
  Qed.

  (* Nothing can be picked from an empty list. *)
  Goal forall (a : @Process Request Reply), Pick [] a [] -> False.
  Proof.
    intros a H.
    pick_case rq H.
    exact H.
  Qed.

  (* Peeling a known-different head from a Pick. *)
  Goal forall (a b : @Process Request Reply)
             (l r : list (@Process Request Reply)),
    a <> b ->
    Pick (a :: l) b r ->
    exists r2, r = a :: r2 /\ Pick l b r2.
  Proof.
    intros a b l r Hne H.
    pick_cons rq H Hne.
    exists rq_tl2.
    split.
    - exact Hrq_eq.
    - exact H.
  Qed.

  (* Case analysis on a pick produced by [vm_step]. *)
  Goal forall (p : Pid) (mb : Set) (req : Request)
             (cnt : Reply req -> Program mb) (rep : Reply req)
             (vm0 vm2 : VM),
    vm0 ~[ts_mfun {| tr_proc := {| pid := p; proc_mb_t := mb;
                                   cont := p_io req cnt |};
                     tr_result := rep |}]~> vm2 ->
    exists rep' : Reply req,
      exists rest : list Process,
        runq vm2 = {| pid := p; proc_mb_t := mb; cont := cnt rep' |} :: rest.
  Proof.
    intros p mb req cnt rep vm0 vm2 H.
    vm_step vm0 H.
    vm_exec vm0 Hvm0_exec.
    pick_case vm0 Hvm0_pick.
    - exists vm0_rep.
      exists vm0_rest.
      reflexivity.
    - exists vm0_rep.
      exists (vm0_hd :: vm0_tl2).
      reflexivity.
  Qed.
End tests.
(* end hide *)
