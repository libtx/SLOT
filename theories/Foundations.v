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

Declare Scope slot_scope.
Open Scope slot_scope.
(* end hide *)

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
Notation "A '~|' R" := (A (fut_result R)) (at level 20) : slot_scope.

Section trans_prod.
  (* Product of transition systems: *)
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
      future s1 ~| r ->
      TransProdFuture (s1, s2) ~| (tpr_l r s2)
  | tpf_cr : forall s1 s2 r,
      future s2 ~| r ->
      TransProdFuture (s1, s2) ~| (tpr_r s1 r).

  Instance transProd : @TransitionSystem State Label TransProdResult :=
    { future := TransProdFuture }.
End trans_prod.

Global Arguments transProd {_ _ _ _ _} (_ _).

Infix "<*>" := (transProd) (at level 98) : slot_scope.

Section trans_sum.
  (* Sum of transition systems: *)
  Context {S1 L1 R1 S2 L2 R2} `{T1 : TransitionSystem S1 L1 R1} `{T2 : TransitionSystem S2 L2 R2}.

  Let State : Type := S1 * S2.

  Let Label : Type := L1 + L2.

  Let Result : Type := R1 * R2.

  Inductive TransSumFuture : State -> @Future State Label Result -> Prop :=
  | tsf_rr : forall s1 s2 r1 r2,
      future s1 ~| r1 ->
      future s2 ~| r2 ->
      TransSumFuture (s1, s2) ~| (r1, r2)
  | tsf_l : forall s1 s1' s2 label,
      future s1 ~[label]~> s1' ->
      TransSumFuture (s1, s2) ~[inl label]~> (s1', s2)
  | tsf_r : forall s1 s2 s2' label,
      future s2 ~[label]~> s2' ->
      TransSumFuture (s1, s2) ~[inr label]~> (s1, s2').

  Instance transSum : @TransitionSystem State Label Result :=
    { future := TransSumFuture }.
End trans_sum.

Global Arguments transSum {_ _ _ _ _ _} (_ _).

Infix "<+>" := (transSum) (at level 99) : slot_scope.

Section state_reachability.
  Context `{HT : TransitionSystem}.

  Inductive ReachableBy : State -> list Label -> State -> Prop :=
  | tsrb_nil : forall s,
      ReachableBy s [] s
  | tsrb_cons : forall s s' s'' label trace,
      future s ~[label]~> s' ->
      ReachableBy s' trace s'' ->
      ReachableBy s (label :: trace) s''.

  Definition HoareTriple (precondition  : State -> Prop)
                         (trace         : list Label)
                         (postcondition : State -> Prop) :=
    forall s s',
      ReachableBy s trace s' -> precondition s ->
      postcondition s'.
End state_reachability.

Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b) (at level 40) : slot_scope.
Notation "'{{}}' t '{{' b '}}'" := (HoareTriple (const True) t b) (at level 39) : slot_scope.

Inductive TraceInvariant `{TransitionSystem} (prop : State -> Prop) : list Label -> Prop :=
| inv_nil :
    TraceInvariant prop []
| inv_cons : forall label trace,
    {{prop}} [label] {{prop}} ->
    TraceInvariant prop trace ->
    TraceInvariant prop (label :: trace).

Section result_reachability.
  Context `{HT : TransitionSystem}.

  Inductive RReachableBy : State -> list Label -> Result -> Prop :=
  | tsrrb_nil : forall s result,
      future s ~| result ->
      RReachableBy s [] result
  | tsrrbt_cons : forall s s' label trace result,
      future s ~[label]~> s' ->
      RReachableBy s' trace result ->
      RReachableBy s (label :: trace) result.

  Definition RHoareTriple (precondition  : State -> Prop)
                          (trace         : list Label)
                          (postcondition : Result -> Prop) :=
    forall s result,
      RReachableBy s trace result -> precondition s ->
      postcondition result.
End result_reachability.

Notation "'{{' a '}}' t '{<' b '>}'" := (RHoareTriple a t b) (at level 40) : slot_scope.
Notation "'{{}}' t '{<' b '>}'" := (RHoareTriple (const True) t b) (at level 39) : slot_scope.

(* begin hide *)
Global Arguments In {_}.
Global Arguments Complement {_}.
Global Arguments Disjoint {_}.
(* end hide *)

Section trace_ensembles.
  Context `{HT : TransitionSystem}.

  Definition TraceEnsemble := Ensemble (list Label).

  (** Hoare logic of trace ensembles consists of a single rule: *)
  Definition EHoareTriple (precondition  : State -> Prop)
                          (ensemble      : TraceEnsemble)
                          (postcondition : State -> Prop) :=
    forall t, In ensemble t ->
         {{ precondition }} t {{ postcondition }}.

  Definition EnsembleInvariant (prop : State -> Prop) (ens : TraceEnsemble) : Prop :=
    forall (t : list Label), ens t -> TraceInvariant prop t.

  (** Hoare logic of trace ensembles consists of a single rule: *)
  Definition ERHoareTriple (precondition  : State -> Prop)
                           (ensemble      : TraceEnsemble)
                           (postcondition : Result -> Prop) :=
    forall t, In ensemble t ->
              {{ precondition }} t {< postcondition >}.
End trace_ensembles.

Notation "'-{{' a '}}' e '{{' b '}}'" := (EHoareTriple a e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{{' b '}}'" := (EHoareTriple (const True) e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{{}}'" := (forall t, e t -> exists s s', ReachableBy s t s')(at level 38) : slot_scope.

Notation "'-{{' a '}}' e '{<' b '>}'" := (ERHoareTriple a e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{<' b '>}'" := (ERHoareTriple (const True) e b)(at level 40) : slot_scope.

Section commutativity.
  Section defn.
    Context `{HT : TransitionSystem}.

    Definition labels_commute (l1 l2 : Label) : Prop :=
      forall (s s' : State),
        ReachableBy s [l1; l2] s' <-> ReachableBy s [l2; l1] s'.

    Global Instance events_commuteSymm : Symmetric labels_commute.
    Proof.
      intros a b Hab s s''.
      unfold labels_commute in *. specialize (Hab s s'').
      now symmetry in Hab.
    Qed.
  End defn.

  Section summ.
    Context {S1 L1 R1 S2 L2 R2 : Type}
      `{T1 : TransitionSystem S1 L1 R1} `{T2 : TransitionSystem S2 L2 R2}.

    Lemma transition_system_sum_comm (l1 : L1) (l2 : L2) :
      @labels_commute _ _ _ (T1 <+> T2) (inl l1) (inr l2).
    Proof.
      unfold labels_commute. intros s s'.
      split; sauto.
    Qed.
  End summ.

  Section product.
    Context {Label S1 R1 S2 R2 : Type}
      `{T1 : TransitionSystem S1 Label R1} `{T2 : TransitionSystem S2 Label R2}.

    Lemma transition_system_prod_comm (l1 : Label) (l2 : Label) :
      @labels_commute _ _ _ T1 l1 l2 ->
      @labels_commute _ _ _ T2 l1 l2 ->
      @labels_commute _ _ _ (T1 <*> T2) l1 l2.
    Proof.
      unfold labels_commute. intros Hl Hr [s_l s_r] [s_l'' s_r''].
      split; intros H.
      - specialize (Hl s_l s_l''). specialize (Hr s_r s_r'').
        inversion_clear H; inversion_clear H1; inversion_clear H2; subst.
        simpl in *.
        constructor 2 with (s' := s').
        simpl.

        inversion_clear H0.
        inversion_clear H.
        simpl in *.
    Abort.
  End product.
End commutativity.


Section canonical_order.
  Class CanonicalOrder (Label : Type) :=
    {
      canon_rel : relation Label;
      canon_decidable a b : {canon_rel a b} + {~canon_rel a b};
      canon_trans : Transitive canon_rel;
      canon_irrefl : Irreflexive canon_rel;
    }.

  Section comm.
    Context `{TransitionSystem} `{CanonicalOrder Label}.

    Definition can_follow (a b : Label) :=
      (~labels_commute a b) \/ (canon_rel a b).

    Definition can_follow_hd (label : Label) (trace : list Label) : Prop :=
      match trace with
      | [] => True
      | head :: _ => can_follow label head
      end.

    Inductive CanonicalTrace : list Label -> Prop :=
    | canontr_nil : CanonicalTrace []
    | canontr_cons : forall label trace,
        can_follow_hd label trace ->
        CanonicalTrace trace ->
        CanonicalTrace (label :: trace).

    Theorem canon_trace_replacement  :
      (forall t,



  End comm.
End canonical_order.

(** ** State space

[StateSpace] class is an abstraction used to describe side effects of
syscalls.

*** Parameters:

 - <<State>> — set of points of the state space

 - <<Event>> — set of events

*** Methods:

[state_transition s e s'] is a type of statements that read as "Event
[e] can transition the system from state [s] to [s']".

 *)
Class StateSpace (State Event : Type) :=
  { state_transition : State -> Event -> State -> Prop;
  }.

Notation "a '~[' b ']~>' c" := (state_transition a b c)(at level 40) : slot_scope.

(** For example suppose <<S>> is [nat] and <<TE>> is [Inductive TE := increment.]

Then the state transition method for the side effects of <<TE>> can be defined like this:

[[
state_transition s event s' =
  match event with
  | increment => s' = s + 1
  end.
]]

Note that side effects can be nondeterminisic. Let's extend our definition
of TE with "Russian roulette" operation that either leaves the state unchanged
or sets it to zero:

[[
Inductive TE := increment
              | rr.
]]

State transition predicate for this operation will look like this:

[[
state_transition s event s'  =
  match event with
  | increment => s' = s + 1
  | rr        => s' = s \/ s' = 0
  end.
]]

*)

(** ** Paths through the state space

[ReachableByTrace] is a datatype describing paths through the state space. Its
first constructor [rbt_nil] states the fact that the empty trace
doesn't change the state of the system. In other words, state of the
system doesn't drift by itself.

The second constructor [rbt_cons] declares that performing a syscall
[te] transitioning the system from [s] to [s'] followed by execution
of all syscalls in [trace], transitioning the system from [s'] to
[s''], is equivalent to executing a path [te :: trace] from [s] to
[s''] *)

Section reachable_by_trace.
  Context `{StateSpace}.

  Inductive ReachableByTrace : State -> list Event -> State -> Prop :=
  | rbt_nil : forall s,
      ReachableByTrace s [] s
  | rbt_cons : forall s s' s'' evt trace,
      s ~[evt]~> s' ->
      ReachableByTrace s' trace  s'' ->
      ReachableByTrace s (evt :: trace) s''.
End reachable_by_trace.

(** ** Hoare logic of traces

    [HoareTriple] is a type of judgments about trace execution,
    stating that if precondition [pre] holds for the initial state
    [s], and there is path [trace] through the state space leading
    to a point [s'], then postcondition [post] must hold for
    [s']. *)
Section hoare.
  Context `{StateSpace}.

  Definition HoareTriple (precondition  : State -> Prop)
                         (trace         : list Event)
                         (postcondition : State -> Prop) :=
    forall s s',
      ReachableByTrace s trace s' -> precondition s ->
      postcondition s'.
End hoare.

(* begin details *)
Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b) (at level 40) : slot_scope.
Notation "'{{}}' t '{{' b '}}'" := (HoareTriple (const True) t b) (at level 39) : slot_scope.
(* end details *)

(** ** Invariants

  [TraceInvariant] is a type of judgments stating that if execution
  of a trace starts in a state where property [prop] holds, then the
  same property will hold for each intermediate state during
  execution of the trace. In other words: [prop] is a subset of the
  state space, and if the system starts off in this subset, it always
  stays in it.
*)

Inductive TraceInvariant `{StateSpace} (prop : State -> Prop) : list Event -> Prop :=
| inv_nil :
    TraceInvariant prop []
| inv_cons : forall te t,
    {{prop}} [te] {{prop}} ->
    TraceInvariant prop t ->
    TraceInvariant prop (te :: t).

Definition PossibleTrace `{Hssp : StateSpace} t :=
  exists s s', ReachableByTrace s t s'.

Definition TraceSpec `{Hssp : StateSpace} (spec : list Event -> Prop) :=
  forall t,
    spec t <-> PossibleTrace t.

(** * Ensembles of traces

    Trace ensembles play one of central roles in SLOT, because from
    SLOT point of view any system is nothing but a collection of event
    traces that it can produce.
 *)

(* begin hide *)
Global Arguments In {_}.
Global Arguments Complement {_}.
Global Arguments Disjoint {_}.
(* end hide *)

Section ensembles.
  Context `{StateSpace}.

  Definition TraceEnsemble := Ensemble (list Event).

  (** Hoare logic of trace ensembles consists of a single rule: *)
  Definition EHoareTriple (precondition  : State -> Prop)
                          (ensemble      : TraceEnsemble)
                          (postcondition : State -> Prop) :=
    forall t, In ensemble t ->
         {{ precondition }} t {{ postcondition }}.

  Definition EnsembleInvariant (prop : State -> Prop) (ens : TraceEnsemble) : Prop :=
    forall (t : list Event), ens t -> TraceInvariant prop t.
End ensembles.

(* begin details *)
Global Arguments TraceEnsemble : clear implicits.

Notation "'-{{' a '}}' e '{{' b '}}'" := (EHoareTriple a e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{{' b '}}'" := (EHoareTriple (const True) e b)(at level 40) : slot_scope.
Notation "'-{{}}' e '{{}}'" := (forall t, e t -> exists s s', ReachableByTrace s t s')(at level 38) : slot_scope.
(* end details *)


(** ** Process ID in SLOT is a natural number: *)
Definition PID := nat.

Record ProcessEvent {Event : Type} :=
  proc_te { te_pid : PID;
            te_event : Event
          }.

(* begin hide *)
Global Arguments ProcessEvent : clear implicits.
Global Arguments proc_te {_}.
(* end hide *)

(* begin details *)
Notation "p @ t" := (proc_te p t) (at level 50) : slot_scope.
(* end details *)

(** * Input/output

 *)


Record IOp (Request : Type) (Reply : Request -> Type) :=
  iop { iop_req : Request;
        iop_rep : Reply iop_req;
      }.

Global Arguments iop {_ _} iop_req iop_rep.

Notation "a <~ b" := (iop b a) (at level 49).

Definition TraceElem (Request : Type) (Reply : Request -> Type) := ProcessEvent (IOp Request Reply).
Definition Trace (Request : Type) (Reply : Request -> Type) := list (TraceElem Request Reply).

Class IOHandler {Request : Type} {Reply : Request -> Type} : Type :=
  mkHandler
    { h_state : Type;
      h_state_transition : h_state -> TraceElem Request Reply -> h_state -> Prop;
    }.

Global Instance handlerStateSpace `{IOHandler} : StateSpace h_state (TraceElem Request Reply) :=
  {| state_transition := h_state_transition |}.

(** * Single thread program

 *)

CoInductive Program {Request : Type} {Reply : Request -> Type} {Ret : Type} : Type :=
| p_dead : (* Program terminted *)
    Ret -> Program
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
(* end details *)

(** * Concurrency

 Now let's introduce concurrency. We represent concurrent processes by
 interleaving of traces.

 *)

Section interleaving.
  Context {Event : Type}.

  (** Set of all possible interleaving of two traces is a trace
  ensemble. As we later prove in [interleaving_to_permutation], this
  definition is dual to [Permutation] of two traces. *)
  Inductive Interleaving : list Event -> list Event -> TraceEnsemble Event :=
  | ilv_cons_l : forall te t1 t2 t,
      Interleaving t1 t2 t ->
      Interleaving (te :: t1) t2 (te :: t)
  | ilv_cons_r : forall te t1 t2 t,
      Interleaving t1 t2 t ->
      Interleaving t1 (te :: t2) (te :: t)
  | ilv_nil : Interleaving [] [] [].
End interleaving.
