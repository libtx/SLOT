From Stdlib Require Import
  Program
  Decidable
  List
  Ensembles
  Relation_Definitions
  RelationClasses
  SetoidClass
  SetoidDec
  Classes.Morphisms.

Import ListNotations.

From Hammer Require Import
  Tactics.

From SLOT Require Import
  Setoids
  RestrictedPermutation
  Multifunction
  TokenMachine.

Export Multifunction TokenMachine.

Section TransitionSystem.
  Context {State : Type}.

  Definition ts_ret (Event : Type) := option (Event * State).

  Definition ts_ret_setoid (Event : Type) (Hss : Setoid State) :=
    let sp := @pair_setoid Event State (eq_setoid _) Hss in
    @setoid_option (Event * State) sp.

  Class TransitionSystem {Event : Type} :=
    {
      ts_setoid :: Setoid State;
      ts_canon_rel : relation Event;
      ts_canon_order :: CanonicalOrder ts_canon_rel;
      ts_state_trans :: @MFun State (ts_ret Event) ts_setoid (ts_ret_setoid Event ts_setoid);
    }.

  Program Definition ts_mfun `{TransitionSystem} (e : Event) : MFun State State :=
    {| morphism s s' :=
        s ~[ts_state_trans]~> Some (e, s');
    |}.
  Next Obligation.
    sauto.
  Qed.

  Global Instance tsTokenSystem `{TransitionSystem} : @TokenMachine State Event :=
    { tm_setoid := ts_setoid;
      tm_canon_rel := ts_canon_rel;
      tm_canon_order := ts_canon_order;
      tm_state_trans := ts_mfun;
    }.

  Definition ts_event_commute `{TransitionSystem} (a b : Event) := commute (ts_mfun a) (ts_mfun b).
End TransitionSystem.

Section TSProps.
  Context `{HTS : TransitionSystem}
           (Hcanon_dec : forall f g : Event, decidable (ts_event_commute f g)).

  (* TODO: this is an mfun *)
  Inductive TSMFunGen : State -> list Event -> State -> Prop :=
  | ts_nil : forall s,
      s ~[ts_state_trans]~> None ->
      TSMFunGen s [] s
  | ts_cont : forall s s' s'' t event,
      TSMFunGen s' t s'' ->
      s ~[ts_state_trans]~> Some (event, s') ->
      TSMFunGen s (event :: t) s''.

  Lemma transition_system_as_token_machine_trace (s s' : State) (t : list Event) :
    TSMFunGen s t s' ->
      s ~[compose_list (map tm_state_trans t)]~> s'.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - destruct t; simpl in *.
      + inversion H. now subst.
      + exists s'. now split.
  Qed.

  Lemma tsfun_gen_as_te s s' : sufficient_replacement_p
                                 (fun t => TSMFunGen s t s')
                                 (fun t => exists{s'' == s'}, CanonicalTrace t s s'').
  Proof.
    intros t Ht.
    apply transition_system_as_token_machine_trace in Ht.
    now apply canonicalize_trace in Ht.
  Qed.

  Definition can_follow_ts (a b : Event) :=
    event_commute a b -> ts_canon_rel a b.

  Definition can_follow_hd_ts (token : Event) (trace : Trace) : Prop :=
    match trace with
    | [] => True
    | head :: _ =>
        can_follow_ts token head
    end.

  Lemma can_follow_equiv a b : can_follow a b <-> can_follow_ts a b.
  Proof.
    sauto.
  Qed.

  Lemma can_follow_hd_equiv a t : can_follow_hd a t <-> can_follow_hd_ts a t.
  Proof.
    sauto.
  Qed.

  Inductive CanonicalTSMFunGen : State -> list Event -> State -> Prop :=
  | cts_nil : forall s,
      s ~[ts_state_trans]~> None ->
      CanonicalTSMFunGen s [] s
  | cts_cons : forall s s' s'' event trace,
      s ~[ts_state_trans]~> Some (event, s') ->
      can_follow_hd_ts event trace ->
      CanonicalTSMFunGen s' trace s'' ->
      CanonicalTSMFunGen s (event :: trace) s''.

  Lemma canon_ts_mfun_trace_is_always_canonical s s' t :
    CanonicalTSMFunGen s t s' -> CanonicalTrace t s s'.
  Proof.
    intros H.
    induction H.
    - constructor.
    - now constructor 2 with (s' := s').
  Qed.

  Theorem canonicalize_transition_system : forall s s' t,
      TSMFunGen s t s' ->
      exists t', exists{s'' == s'},
        CanonicalTSMFunGen s t' s''.
  Proof.
    intros.
    specialize (transition_system_as_token_machine_trace s s' t H) as Hss'.
    specialize (canonicalize_trace Hcanon_dec s s' t) as Hcan.
    simpl in Hcan. apply Hcan in Hss'. clear Hcan.
    destruct Hss' as [t' Ht'].
    exists t'.
    destruct Ht' as [[s'' [Hss'' Heq]] Ht'].
    exists s''.
    split; [|assumption].
  Abort.
End TSProps.
