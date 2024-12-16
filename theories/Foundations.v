(* SLOT, proofs about distributed systems design
   Copyright (C) 2019-2024  k32

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

(** * Fundamental definitions for modeling the nondeterminisic concurrent systems
 *)

(* begin hide *)
From Coq Require Import
  Program
  List
  Ensembles
  Relation_Definitions
  RelationClasses.

Import ListNotations.

From Hammer Require Import
  Tactics.

From SLOT Require Export
  RestrictedPermutation.

Declare Scope slot_scope.
Open Scope slot_scope.
(* end hide *)

(* begin hide *)
Global Arguments In {_}.
Global Arguments Complement {_}.
Global Arguments Disjoint {_}.
(* end hide *)

(** * Nondeterministic Labeled Transition System

[TransitionSystem] class is the base abstraction of SLOT. It is used
both to describe side effects of syscalls, as well as state of the
process scheduler.

[Future] is a datatype that represents valid transitions:

 - [fut_cont] constructor represents a state transition via a label

 - [fut_result] constructor represents a terminal state producing
   result of a computation

*** Parameters:

 - <<State>> — set of points of the state space

 - <<Label>> — set of transitions

 - <<Result>> — set of results

*** Methods:

[future s Future] represents a valid state transition.

*)

Section transition_system.
  Context {State Label Result : Type}.

  Inductive Future :=
  | fut_cont : Label -> State -> Future
  | fut_result : Result -> Future.

  Class TransitionSystem :=
    { future : State -> Future -> Prop
    }.
End transition_system.

Global Arguments TransitionSystem (_ _ _) : clear implicits.

Notation "A '~[' L ']~>' S" := (A (fut_cont L S)) (at level 20) : slot_scope.
Notation "A '~>[' R ']'"  := (A (fut_result R)) (at level 20) : slot_scope.

(** ** Paths through the state space

[Trace] is a datatype describing paths through the state space. Its
first constructor [tr_nil] states the fact that empty trace doesn't
change the state of the system. In other words, state of the system
doesn't drift by itself.

The second constructor [tr_cons] declares that transition [label] that
changes state of the system from [s] to [s'] followed by applying all
labels in [trace] to [s'], resulting in state [s''], is equivalent to
executing a trace [te :: trace], transitioning the system from [s] to
[s'']

*)

Section state_reachability.
  Context `{HT : TransitionSystem}.

  Inductive Trace : State -> State -> list Label -> Prop :=
  | tr_nil : forall s,
      Trace s s []
  | tr_cons : forall s s' s'' label trace,
      future s ~[label]~> s' ->
      Trace s' s'' trace ->
      Trace s s'' (label :: trace).

  (** ** Hoare logic of traces

    [HoareTriple] is a type of judgments about trace execution,
    stating that if precondition [pre] holds for the initial state
    [s], and there is path [trace] through the state space leading to
    state [s'], then postcondition [post] must hold for [s']. *)
  Definition HoareTriple (precondition  : State -> Prop)
                         (trace         : list Label)
                         (postcondition : State -> Prop) :=
    forall s s',
      Trace s s' trace -> precondition s ->
      postcondition s'.

  (** ** Hoare triple for terminal states

    [RHoareTriple] is a type of judgments about trace execution,
    stating that if precondition [pre] holds for the initial state
    [s], and [trace] leads to some terminal state with result
    [result], then postcondition [post] must hold for [result]. *)
  Definition RHoareTriple (precondition  : State -> Prop)
                          (trace         : list Label)
                          (postcondition : Result -> Prop) :=
    let postcondition' s := exists2 result, future s ~>[ result ] & postcondition result
    in HoareTriple precondition trace postcondition'.
End state_reachability.

Global Arguments Trace {_ _ _} (_).

Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b) (at level 40) : slot_scope.
Notation "'{{}}' t '{{' b '}}'" := (HoareTriple (const True) t b) (at level 39) : slot_scope.

Notation "'{{' a '}}' t '{<' b '>}'" := (RHoareTriple a t b) (at level 40) : slot_scope.
Notation "'{{}}' t '{<' b '>}'" := (RHoareTriple (const True) t b) (at level 39) : slot_scope.

(** ** Invariants

  [StateInvariant] is a type of judgments stating that if execution
  of a trace starts in a state where property [prop] holds, then the
  same property will hold for each intermediate state during
  execution of the trace. In other words: [prop] is a subset of the
  state space, and if the system starts off in this subset, it always
  stays in it.
*)
Section state_invariant.
  Context `{HT : TransitionSystem} (invariant : State -> Prop).

  Let invariant_future s f := future s f \/ invariant s.

  Local Instance invTransSys : @TransitionSystem State Label Result :=
    {
      future := invariant_future
    }.

  Definition StateInvariant (trace : list Label) : Prop :=
    forall s s',
      Trace invTransSys s s' trace.
End state_invariant.

(** * Ensembles of traces

    Trace ensembles play one of central roles in SLOT, because from
    SLOT point of view any system is nothing but a collection
    (ensemble) of event traces that it can produce. *)
Section trace_ensembles.
  Context `{HT : TransitionSystem}.

  Definition TraceEnsemble := Ensemble (list Label).

  (** Hoare logic of trace ensembles consists of a single rule: *)
  Definition EHoareTriple (precondition  : State -> Prop)
                          (ensemble      : TraceEnsemble)
                          (postcondition : State -> Prop) :=
    forall t, In ensemble t ->
         {{ precondition }} t {{ postcondition }}.

  (** Same, but for the results: *)
  Definition ERHoareTriple (precondition  : State -> Prop)
                           (ensemble      : TraceEnsemble)
                           (postcondition : Result -> Prop) :=
    forall t, In ensemble t ->
              {{ precondition }} t {< postcondition >}.

  Definition OccupiedTraceEnsemble (e : TraceEnsemble) : Prop :=
    exists t s s',
      e t -> Trace HT s s' t.

  Definition FullyOccupiedTraceEnsemble (e : TraceEnsemble) : Prop :=
    forall t,
      e t -> exists s s', Trace HT s s' t.
End trace_ensembles.

Notation "'-{{' a '}}' e '{{' b '}}'" := (EHoareTriple a e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{{' b '}}'" := (EHoareTriple (const True) e b)(at level 40) : slot_scope.

Notation "'-{{' a '}}' e '{<' b '>}'" := (ERHoareTriple a e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{<' b '>}'" := (ERHoareTriple (const True) e b)(at level 40) : slot_scope.

Section commutativity.
  Section defn.
    Context `{TS : TransitionSystem}.

    Definition labels_commute (l1 l2 : Label) : Prop :=
      forall (s s' : State),
        Trace TS s s' [l1; l2] <-> Trace TS s s' [l2; l1].

    Global Instance events_commuteSymm : Symmetric labels_commute.
    Proof.
      intros a b Hab s s''.
      unfold labels_commute in *. specialize (Hab s s'').
      now symmetry in Hab.
    Qed.
  End defn.
End commutativity.

Section trace_properties.
  Context `{TS : TransitionSystem}.

  (** [trace_split] is an important observation that there is a point
  in the state space for each intermediate step of the trace
  execution: *)
  Lemma trace_split : forall s s'' t1 t2,
      Trace TS s s'' (t1 ++ t2) ->
      exists s', Trace TS s s' t1 /\ Trace TS s' s'' t2.
  Proof with sauto.
    intros.
    generalize dependent s.
    induction t1; intros.
    - exists s. split...
    - simpl in H.
      inversion_clear H.
      specialize (IHt1 s' H1).
      destruct IHt1.
      exists x. split...
  Qed.

  (** [trace_concat] lemma demonstrates that traces can be composed: *)
  Lemma trace_concat : forall s s' s'' t1 t2,
      Trace TS s s' t1 ->
      Trace TS s' s'' t2 ->
      Trace TS s s'' (t1 ++ t2).
  Proof with sauto.
    intros.
    generalize dependent s.
    induction t1...
  Qed.

  Lemma trace_commutateive_permutation s s' t t' :
    Trace TS s s' t ->
    RestrictedPermutation labels_commute t t' ->
    Trace TS s s' t'.
  Proof with sauto.
    intros Hls Hperm.
    generalize dependent s.
    induction Hperm; intros; try sauto.
    - replace (a :: b :: l) with ([a; b] ++ l) in Hls by reflexivity.
      replace (b :: a :: l) with ([b; a] ++ l) by reflexivity.
      apply trace_split in Hls.
      destruct Hls as [s_ [Hs_ Hs']].
      apply H in Hs_.
      apply trace_concat with (s' := s_)...
  Qed.
End trace_properties.

Section trace_equivalence.
  Context `{T : TransitionSystem} (e e' : @TraceEnsemble Label).

  Definition sufficient_replacement :=
    forall t s s', e t ->
              Trace T s s' t ->
              exists t', e' t' /\ Trace T s s' t'.

  Definition sufficient_replacement_p :=
    forall t, e t ->
         exists t', e' t' /\ RestrictedPermutation labels_commute t t'.

  Theorem ht_sufficient_replacement P Q :
    sufficient_replacement ->
    -{{P}} e' {{Q}} -> -{{P}} e {{Q}}.
  Proof.
    intros He2 Heht t Ht s s' Hls Hpre.
    destruct (He2 t s s' Ht Hls) as [t' [Ht' Hls']].
    eapply Heht; eauto.
  Qed.

  Lemma comm_perm_sufficient_replacement :
    sufficient_replacement_p ->
    sufficient_replacement.
  Proof.
    intros Hsrp t s s' Ht Hls.
    destruct (Hsrp t Ht) as [t' [Ht' Hperm]].
    eapply trace_commutateive_permutation in Hperm; eauto.
  Qed.
End trace_equivalence.

(** * Product of transition systems *)
Section trans_prod.
  Context {Label S1 S2 R1 R2 : Type}
    `{T1 : TransitionSystem S1 Label R1} `{T2 : TransitionSystem S2 Label R2}.

  Let State : Type := S1 * S2.

  Inductive TransProdResult :=
  | tpr_l : forall (result_left : R1) (state_right  : S2), TransProdResult
  | tpr_r : forall (state_left  : S1) (result_right : R2), TransProdResult.

  Inductive TransProdFuture : State -> @Future State Label TransProdResult -> Prop :=
  | tpf_cc : forall (label : Label) (s1 s1' : S1) (s2 s2' : S2),
      future s1 ~[label]~> s1' ->
      future s2 ~[label]~> s2' ->
      TransProdFuture (s1, s2) ~[label]~> (s1', s2')
  | tpf_rc : forall s1 s2 r,
      future s1 ~>[r] ->
      TransProdFuture (s1, s2) ~>[tpr_l r s2]
  | tpf_cr : forall s1 s2 r,
      future s2 ~>[r] ->
      TransProdFuture (s1, s2) ~>[tpr_r s1 r].

  Instance transProd : @TransitionSystem State Label TransProdResult :=
    { future := TransProdFuture }.

  Lemma transition_system_prod_comm (l1 : Label) (l2 : Label) :
    @labels_commute _ _ _ T1 l1 l2 ->
    @labels_commute _ _ _ T2 l1 l2 ->
    @labels_commute _ _ _ transProd l1 l2.
  Proof.
    unfold labels_commute, transProd.
    intros HT1 HT2 [s_l s_r] [s''_l s''_r].
    specialize (HT1 s_l s''_l). specialize (HT2 s_r s''_r).
    split; intros H.
    { inversion H. clear H. inversion H5. clear H5. inversion H10. clear H10. subst.
      destruct s' as [s'_l s'_r].
      inversion_clear H4. inversion_clear H9.
      destruct HT1 as [HT1 _]. destruct HT2 as [HT2 _].
      assert (HT1p : Trace T1 s_l s''_l [l1; l2]) by sauto. specialize (HT1 HT1p). clear HT1p.
      assert (HT2p : Trace T2 s_r s''_r [l1; l2] ) by sauto. specialize (HT2 HT2p). clear HT2p.
      sauto.
    }
    { inversion H. clear H. inversion H5. clear H5. inversion H10. clear H10. subst.
      destruct s' as [s'_l s'_r].
      inversion_clear H4. inversion_clear H9.
      destruct HT1 as [_ HT1]. destruct HT2 as [_ HT2].
      assert (HT1p : Trace T1 s_l s''_l [l2; l1]) by sauto. specialize (HT1 HT1p). clear HT1p.
      assert (HT2p : Trace T2 s_r s''_r [l2; l1]) by sauto. specialize (HT2 HT2p). clear HT2p.
      sauto.
    }
  Qed.
End trans_prod.

Global Arguments transProd {_ _ _ _ _} (_ _).

Infix "<*>" := (transProd) (at level 98) : slot_scope.

(** * Sum of transition systems *)
Section trans_sum.
  Context {S1 L1 R1 S2 L2 R2} `{T1 : TransitionSystem S1 L1 R1} `{T2 : TransitionSystem S2 L2 R2}.

  Let State : Type := S1 * S2.

  Let Label : Type := L1 + L2.

  Let Result : Type := R1 * R2.

  Inductive TransSumFuture : State -> @Future State Label Result -> Prop :=
  | tsf_rr : forall s1 s2 r1 r2,
      future s1~>[r1] ->
      future s2~>[r2] ->
      TransSumFuture (s1, s2) ~>[(r1, r2)]
  | tsf_l : forall s1 s1' s2 label,
      future s1 ~[label]~> s1' ->
      TransSumFuture (s1, s2) ~[inl label]~> (s1', s2)
  | tsf_r : forall s1 s2 s2' label,
      future s2 ~[label]~> s2' ->
      TransSumFuture (s1, s2) ~[inr label]~> (s1, s2').

  Instance transSum : @TransitionSystem State Label Result :=
    { future := TransSumFuture }.

  Lemma transition_system_sum_comm (l1 : L1) (l2 : L2) :
    @labels_commute _ _ _ transSum (inl l1) (inr l2).
  Proof.
    unfold labels_commute. intros s s'.
    split; sauto.
  Qed.
End trans_sum.

Global Arguments transSum {_ _ _ _ _ _} (_ _).

Infix "<+>" := (transSum) (at level 99) : slot_scope.

From Coq Require Import
  Decidable.

(** ** Canonical Traces *)
Section canonical_order.
  Class CanonicalOrder {Label} (canon_rel : relation Label) :=
    {
      (* Non-strict total order: *)
      canon_decidable a b : decidable (canon_rel a b);
      canon_total a b : canon_rel a b \/ canon_rel b a;
      canon_trans :: Transitive canon_rel;
      (* Reflexivity is important for ordering of events produced by
      the same process: *)
      canon_reflexive :: Reflexive canon_rel;
      canon_antisymmetric a b := canon_rel a b -> canon_rel b a -> a = b;
    }.

  Section comm.
    Context `{T : TransitionSystem} `{Hcanon : CanonicalOrder Label} (commut_dec : forall a b, decidable (labels_commute a b)).

    Definition can_follow (a b : Label) :=
      (~labels_commute a b) \/ (canon_rel a b).

    Definition can_follow_hd (label : Label) (trace : list Label) : Prop :=
      match trace with
      | [] => True
      | head :: _ =>
          can_follow label head
      end.

    Lemma canon_rel_asymm a b : ~canon_rel a b -> canon_rel b a.
    Proof.
      intros H.
      destruct (canon_total b a); destruct (canon_total a b); firstorder.
    Qed.

    Lemma can_follow_dec a b : decidable (can_follow a b).
    Proof.
      unfold can_follow.
      specialize (commut_dec a b) as Hdcomm.
      specialize (canon_decidable a b) as Hdcanon.
      apply dec_not in Hdcomm.
      apply dec_or; assumption.
    Qed.

    Lemma can_follow_hd_dec a t : decidable (can_follow_hd a t).
    Proof.
      destruct t.
      - simpl. apply dec_True.
      - simpl. apply can_follow_dec.
    Qed.

    Inductive CanonicalTrace : State -> State -> list Label -> Prop :=
    | canontr_nil : forall s,
        CanonicalTrace s s []
    | canontr_cons : forall s s' s'' label trace,
        future s ~[label]~> s' ->
        can_follow_hd label trace ->
        CanonicalTrace s' s'' trace ->
        CanonicalTrace s s'' (label :: trace).

    Lemma can_follow_hd_eq {te t1 t2} (Hfoll : can_follow_hd te t1) (Hhd : hd_error t1 = hd_error t2) :
      can_follow_hd te t2.
    Proof.
      intros.
      unfold can_follow_hd in *.
      destruct t1, t2; try reflexivity.
      - exfalso. inversion Hhd.
      - simpl in Hhd. injection Hhd as H. now subst.
    Qed.

    Fixpoint canon_trace_add s s' s'' label t (Hlabel : future s ~[label]~> s')
                             (Ht : CanonicalTrace s' s'' t)
                             (Hfoll : ~can_follow_hd label t) {struct Ht} :
      exists t', CanonicalTrace s s'' t' /\
                 RestrictedPermutation labels_commute (label :: t) t' /\
                 (hd_error t = hd_error t').
    Proof with sauto.
      inversion Ht as [| A s_ B label' t' Hs_ Hfoll' Ht']; subst; clear Ht.
      - exfalso. (* Hfoll cannot hold for an empty list *)
        clear canon_trace_add.
        unfold not, can_follow_hd in Hfoll.
        contradiction.
      - assert (Hl'lcanon : canon_rel label' label). {
          clear canon_trace_add.
          firstorder.
        }
        assert (Hlcomm : labels_commute label label'). {
          clear canon_trace_add.
          unfold can_follow_hd, can_follow in Hfoll.
          destruct (commut_dec label label').
          + assumption.
          + firstorder.
        }
        (* Use label commutativity to derive an intermediate state on
        the [label'; label] path: *)
        assert (Hll' : Trace T s s_ [label; label']). {
          constructor 2 with s'. assumption. constructor 2 with s_. assumption. constructor.
        }
        apply Hlcomm in Hll'.
        inversion Hll'. inversion H4. inversion H10. subst.
        (* Case analysis: can we attach [label] to [t']? *)
        destruct (can_follow_hd_dec label t') as [Hfoll'' | Hfoll''].
        + (* Yes, we can. Proof by construction: *)
          exists (label' :: label :: t').
          repeat split.
          * constructor 2 with s'0...
          * constructor. assumption.
        + (* No, we cannot. Proof by induction *)
          specialize (canon_trace_add s'0 s_ s'' label t' H9 Ht' Hfoll'').
          destruct canon_trace_add as [t'' [Ht'' [Hcomm'' Hhd'']]].
          exists (label' :: t'').
          repeat split.
          * constructor 2 with s'0; auto.
            eapply can_follow_hd_eq; eauto.
          * sauto.
    Defined.

    Fixpoint canon_trace_ (s s'' : State) (t : list Label) (Ht : Trace T s s'' t)
          {struct Ht} :
      exists t' : list Label, CanonicalTrace s s'' t' /\ RestrictedPermutation labels_commute t t'.
    Proof with sauto.
      destruct Ht.
      - exists []...
      - apply canon_trace_ in Ht. clear canon_trace_. destruct Ht as [t' [Ht' Hperm]].
        destruct (can_follow_hd_dec label t').
        + exists (label :: t')...
        + eapply canon_trace_add in Ht'; eauto.
          destruct Ht' as [t'' [Ht'' [Hperm'' Hhd]]].
          exists t''...
    Qed.

    Theorem canonicalize_trace s s' :
      sufficient_replacement_p (Trace T s s') (CanonicalTrace s s').
    Proof.
      intros t Ht.
      now apply canon_trace_.
    Qed.
  End comm.
End canonical_order.

Require Import ZArith.
Open Scope positive_scope.
Require Import String.

Definition PID : Type := positive * positive.

Inductive ProgramReturn :=
| normal
| error : string -> ProgramReturn.

CoInductive Program {Request : Type} {Reply : Request -> Type} : Type :=
| p_dead : (* Program terminted *)
    ProgramReturn -> Program
| p_spawn : (* Spawn a new process *)
    forall (new : Program)
           (continuation : PID -> Program)
         , Program
| p_cont : (* Program is doing I/O *)
    forall (pending_req : Request)
           (continuation : Reply pending_req -> Program)
         , Program.

(* begin details *)
Notation "'do' V '<-' I ; C" := (p_cont (I) (fun V => C))
    (at level 100, C at next level, V name, right associativity) : slot_scope.

Notation "'return' R" := (p_dead R)
    (at level 100, right associativity) : slot_scope.

Notation "'done' R" := (p_cont (R) (fun _ => p_dead I))
    (at level 100, right associativity) : slot_scope.

Notation "'call' V '<-' I ; C" := (I (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity,
      only parsing) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity) : slot_scope.
(* end details *)

(** * Input/output

 *)

Section iodefs.
  Record IOp (Request : Type) (Reply : Request -> Type) :=
    mk_IOp {
        iop_pid : PID;
        iop_req : Request;
        iop_rep : Reply iop_req;
      }.

  Class IOHandler {Request : Type} {Reply : Request -> Type} : Type :=
    mkHandler
      { h_state : Type;
        h_state_transition : h_state -> IOp Request Reply -> h_state -> Prop;
      }.

  Global Instance ioHandlerTransitionSystem `(IOHandler) : @TransitionSystem h_state (IOp Request Reply) True :=
    {
      future s f :=
        match f with
        | fut_result _ => False
        | fut_cont l s' => h_state_transition s l s'
        end
    }.
End iodefs.

Section trace.
  Context `{IOHandler}.

  Inductive TraceElem :=
  | te_iop : IOp Request Reply -> TraceElem
  | te_spawn : PID -> @Program Request Reply -> PID -> TraceElem
  | te_exit : PID -> ProgramReturn -> TraceElem.
End trace.

(** * Generic scheduler *)
Section gen_scheduler.
  Context {State GlobalState Label : Type}
    (step : GlobalState -> GlobalState -> State -> list State -> Label -> Prop).

  Record SchedulerState :=
    mkSchedState
      { gen_sched_l : list State;
        gen_sched_s : GlobalState;
      }.

  Inductive GenSchedStep : SchedulerState -> @Future SchedulerState Label () -> Prop :=
  | gen_sched_empty : forall s,
      GenSchedStep {| gen_sched_l := []; gen_sched_s := s |} ~>[ () ]
  | gen_sched_skip : forall a s s' l l' te,
      GenSchedStep {| gen_sched_l := l; gen_sched_s := s |} ~[ te ]~> {| gen_sched_l := l'; gen_sched_s := s' |} ->
      GenSchedStep {| gen_sched_l := a :: l; gen_sched_s := s |} ~[ te ]~> {| gen_sched_l := a :: l'; gen_sched_s := s' |}
  | gen_sched_apply : forall a a' s s' l te,
      step s s' a a' te ->
      GenSchedStep {| gen_sched_l := a :: l; gen_sched_s := s |} ~[ te ]~> {| gen_sched_l := a' ++ l; gen_sched_s := s' |}.
End gen_scheduler.

Section node_scheduler.
  Context `{IOHandler}.
  Context (node_id : positive).

  Let Thread : Type := (positive * @Program Request Reply).

  Section prop.
    Context (next_pid : positive).

    Inductive NodeSchedulerStep : positive -> Thread -> list Thread -> @TraceElem Request Reply -> Prop :=
    | nsc_dead :
      forall pid ret,
        let te := te_exit (node_id, pid) ret in
        NodeSchedulerStep
          next_pid
          (pid, p_dead ret)
          []
          te
    | nsc_spawn :
      forall pid new cont,
        let new_pid := (node_id, next_pid) in
        let te := te_spawn (node_id, pid) new new_pid in
        NodeSchedulerStep
          (Pos.succ next_pid)
          (pid, p_spawn new cont)
          [(pid, cont new_pid); (next_pid, new)]
          te
    | nsc_do_iop :
      forall pid request reply cont,
        let te := te_iop (mk_IOp _ _ (node_id, pid) request reply) in
        NodeSchedulerStep
          next_pid
          (pid, p_cont request cont)
          [(pid, cont reply)]
          te.
  End prop.

  Check @SchedulerState.

  Definition NodeSchedulerState : Type := @SchedulerState Thread positive.

  Definition NodeScheduler := GenSchedStep NodeSchedulerStep.
End node_scheduler.

Section network_scheduler.
  Context `{IOH : IOHandler}.

  Definition Node : Type := positive * @NodeSchedulerState Request Reply.

  Inductive NetSchedulerStep : () -> () -> Node -> list Node -> @TraceElem Request Reply -> Prop :=
  | net_sched : forall ns ns' te,
      NodeScheduler ns ~[te]~> ns' ->
      NetSchedulerStep () () ns [ns'] te.


  Inductive NetSchedulerStep : Node -> list Node -> () -> @TraceElem Request Reply -> Prop :=
  | net_sched :
    forall node ns ns' te,
      NodeScheduler node ns ns' te ->
      NetSchedulerStep (node, ns) [(node, ns')] () te.

  Definition NetScheduler (s s' : list Node) (te : @TraceElem Request Reply) : Prop :=
    GenSchedStep NetSchedulerStep s s' () te.
End network_scheduler.

(** * Concurrency

 *)
(* Section interleaving. *)
(*   Context {Event : Type}. *)

(*   (** Set of all possible interleaving of two traces is a trace *) *)
(* (*   ensemble. As we later prove in [interleaving_to_permutation], this *) *)
(* (*   definition is dual to [RestrictedPermutation] of two traces. *) *)
(*   Inductive Interleaving : list Event -> list Event -> Ensemble (list Event) := *)
(*   | ilv_cons_l : forall te t1 t2 t, *)
(*       Interleaving t1 t2 t -> *)
(*       Interleaving (te :: t1) t2 (te :: t) *)
(*   | ilv_cons_r : forall te t1 t2 t, *)
(*       Interleaving t1 t2 t -> *)
(*       Interleaving t1 (te :: t2) (te :: t) *)
(*   | ilv_nil : Interleaving [] [] []. *)
(* End interleaving. *)

(* Section singleton_process. *)
(*   (* Context {Gen State Event} `{StateSpace State (ProcessEvent Event)} `{Generator Event Gen}. *) *)

(*   (* Record SingletonProcess := *) *)
(*   (*   singleton_process { _ : Gen }. *) *)

(*   Inductive SingletonStep : SingletonProcess -> option (SingletonProcess * (ProcessEvent Event)) -> Prop := *)
(*   | wrs_nil : forall g, *)
(*       g ~~>x -> *)
(*       SingletonStep (singleton_process g) None *)
(*   | wrp_cons : forall g g' evt, *)
(*       g ~~> g' & evt -> *)
(*       SingletonStep (singleton_process g) (Some (singleton_process g', 0 @ evt)). *)

(*   Global Instance singletonGen : Generator (ProcessEvent Event) SingletonProcess := *)
(*     { gen_step := SingletonStep }. *)

(*   Lemma singleton_gen_comm : *)
(*     generator_events_commute SingletonProcess. *)
(*   Proof. *)
(*     intros g g' g'' te1 te2 Hpids Hg Hg'. *)
(*     exfalso. *)
(*     inversion Hg; inversion Hg'; subst. *)
(*     sauto. *)
(*   Qed. *)
(* End singleton_process. *)
