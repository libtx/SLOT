(* SLOT, proofs about distributed systems design
   Copyright (C) 2019-2025  k32

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
  RelationClasses
  SetoidClass.

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

*** State class is a setoid.

 *)

Locate "==>".
Check respectful.

Print Setoid.

Print exist.

Section transition_system.
  Context {State Label Result : Type}.

  (* Definition prop_equiv a b (pred : State -> Prop) : *)
  (*   a == b -> *)
  (*   pred a <-> pred b. *)

  (*   Check pointwise_relation. *)

  (* Inductive Eq_prop : relation (State -> Prop) := *)
  (* | eq_prop : forall (a b : State -> Prop), Eq_prop a b. *)

  Class TransitionSystem :=
    { cont : Label -> State -> State -> Prop;

      terminal : State -> Result -> Prop;

      state_setoid :: Setoid State;
    }.

  Print pointwise_relation.


  Add Parametric Morphism `{TransitionSystem} (l : Label) : (cont l)
  with signature (@equiv State state_setoid) ++> (iff) as cont_mor.


      cont_covariant :: equiv ==> equiv

      cont_equiv : forall label s1 s2 s1',
        cont label s1 s1' ->
        s1 == s2 ->
        exists s2',
          cont label s2 s2' /\ s1' == s2';

      terminal_equiv : forall s1 s2 result,
        s1 == s2 ->
        terminal s1 result <-> terminal s2 result;
    }.
  (* This forms a category with two objects: `State' and `Result`, and
     the following morphisms:

     - Label: carrier for the class of identity morphisms
       $id_{State}$
     - terminal: a singleton morphism $Hom(State, Result)$
   *)
End transition_system.

Global Arguments TransitionSystem (_ _ _) : clear implicits.

Notation "A '~[' L ']~>' B" := (cont L A B) (at level 20) :
slot_scope. Notation "A '~>[' R ']'" := (terminal A R) (at level 20) :
slot_scope. Notation "A '~>[]'" := (terminal A I) (at level 21) :
slot_scope.

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

Section state_reachability. Context `{HT : TransitionSystem}.

  Inductive Trace : list Label -> State -> State -> Prop := | tr_nil :
  forall s, Trace [] s s | tr_cons : forall s s' s'' label trace, s
  ~[label]~> s' -> Trace trace s' s'' -> Trace (label :: trace) s s''.

  Lemma trace_equiv trace s1 s1' s2 : Trace trace s1 s1' -> s1 == s2
  -> exists s2', Trace trace s2 s2' /\ s1' == s2'. Proof. intros H1.
  generalize dependent s2. induction H1 as [|s1 s1' s1'' label trace
  Hs1' Hs1'']; intros. - exists s2; sauto. - destruct (cont_equiv
  label s1 s2 s1' H Hs1') as [s2' [Hs2 Hs1's2']]. destruct (IHHs1''
  s2' Hs1's2') as [s2'' [HS2''
  Hs12'']].
  exists s2''. split. + constructor 2 with (s' := s2'); assumption. + assumption. Qed.

  (** ** Hoare logic of traces

    [HoareTriple] is a type of judgments about trace execution,
    stating that if precondition [pre] holds for the initial state
    [s], and there is path [trace] through the state space leading to
    state [s'], then postcondition [post] must hold for [s'].
    *) Definition HoareTriple (precondition : State -> Prop) (trace : list Label) (postcondition : State -> Prop) := forall s s', Trace trace s s' -> precondition s -> postcondition s'.

  (** ** Hoare triple for terminal states

    [RHoareTriple] is a type of judgments about trace execution,
    stating that if precondition [pre] holds for the initial state
    [s], and [trace] leads to some terminal state with result
    [result], then postcondition [post] must hold for [result].
    *) Definition RHoareTriple (precondition : State -> Prop) (trace : list Label) (postcondition : Result -> Prop) := let postcondition' s := exists2 result, s~>[result] & postcondition result in HoareTriple precondition trace postcondition'. End state_reachability.

Global Arguments Trace {_ _ _} (_).


Notation "'{{' a '}}' t '{{' b '}}'" := (HoareTriple a t b) (at level 40) : slot_scope. Notation "'{{}}' t '{{' b '}}'" := (HoareTriple (const True) t b) (at level 39) : slot_scope.

Notation "'{{' a '}}' t '{<' b '>}'" := (RHoareTriple a t b) (at level 40) : slot_scope. Notation "'{{}}' t '{<' b '>}'" := (RHoareTriple (const True) t b) (at level 39) : slot_scope.

(** ** Invariants

  [StateInvariant] is a type of judgments stating that if execution of
  a trace starts in a state where property [prop] holds, then the same
  property will hold for each intermediate state during execution of
  the trace. In other words: [prop] is a subset of the state space,
  and if the system starts off in this subset, it always stays in it.
  *) Section state_invariant. Context `{HT : TransitionSystem} (invariant : State -> Prop).

  Let invariant_future s f := future s f \/ invariant s.

  Local Instance invTransSys : @TransitionSystem State Label Result := { future := invariant_future }.

  Definition StateInvariant (trace : list Label) : Prop := forall s s', Trace invTransSys s s' trace. End state_invariant.
