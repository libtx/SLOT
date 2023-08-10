(* SLOT, a formally verified model checker
   Copyright (C) 2021-2023  k32

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

From SLOT Require Export
     Foundations
     Generator
     Commutativity
     Handlers
     Tactics.

From Coq Require Import
     Lia.

From Hammer Require Import
     Tactics.

From Coq Require Import List.
Import ListNotations.

(* begin: hide *)
Require Handlers.Deterministic
        Handlers.Mutex.

From Ltac2 Require Import Init List Ind Env Control Option Constr Std Array Notations Fresh Printf.
(* end: hide *)

Module Example.
  Import Handlers.Deterministic Handlers.Deterministic.Var Mutex.

  Inductive handlerId := var | mutex.

  Ltac2 handlerSpec () := ['(Var.t nat); 'Mutex.t].

  Definition handler := ltac2:(makeClass handlerSpec).
  Definition reqT := ltac2:(makeRequestType handlerSpec 'handlerId).
  Definition req := ltac2:(makeReq handlerSpec 'handlerId 'reqT 'handler).
  Definition stateG := ltac2:(makeStateGetter handlerSpec 'handler 'handlerId).
  Definition Req := handler_request_t handler.
  Definition Rep := handler_reply_t handler.
  Definition TE := ProcessEvent (@IOp Req Rep).

  Definition prog : @Program Req Rep :=
    do _ <- req mutex grab;
    do x <- req var read;
    do _ <- req var (write (x + 1));
    done (req mutex release).

  Import better_parallel.

  Definition system := of_progs [prog; prog].

  Lemma canned_par_opt_nil {last_pid}
    {t : Trace Req Rep}
    (H : GenEnsembleOpt {| last_pid := last_pid; processes := []|} t) :
    t = [].
  Proof.
    inversion H.
    - reflexivity.
    - inversion H0.
  Qed.

  Lemma canned_par_opt_two {last_pid p rest}
    {t : Trace Req Rep}
    (H : GenEnsembleOpt {| last_pid := last_pid; processes := p :: rest|} t) :
    exists g' te t',
      t = te :: t' /\
      {| last_pid := last_pid; processes := p :: rest|} ~~> g' & te /\
        can_follow_hd te t' /\
        GenEnsembleOpt g' t'.
  Admitted.

Section tests.

  (* Ltac clauses H := *)
  (*   lazymatch type of H with *)
  (*   | ?A \/ ?B => destruct H as [H|H]; [idtac|clauses H] *)
  (*   | _ => idtac *)
  (*   end. *)

  Ltac2 elim_by_comm (hi : ident) :=
    let hpid := in_goal @Hpid in
    let hnoncomm := in_goal @Hnoncomm in
    let hcomm := in_goal @Hcomm in
    let h := hyp hi in
    let try_find_comm () :=
      lazy_match! type (hyp hnoncomm) with
        ~ events_commute ?a ?b => assert ($hcomm : events_commute $a $b) by (* auto with slot_comm *)
          first [apply compose_comm | apply compose_comm_rev]      end;
      let h1 := hyp hnoncomm in
      let h2 := hyp hcomm in
      now (destruct ($h1 $h2)) in
    destruct $h as [$hpid|$hnoncomm] > [ltac1:(lia) | try_find_comm ()].

  Goal forall t (rep1 rep2 : nat) , can_follow_hd (1 @ rep1 <~ inl read) [0 @ rep2 <~ inr read; t] -> False.
  Proof.
    intros.
    elim_by_comm @H.
  Qed.

  Goal forall t (rep1 rep2 : nat) , can_follow_hd (1 @ rep1 <~ inr read) [0 @ rep2 <~ inl read; t] -> False.
  Proof.
    intros.
    elim_by_comm @H.
  Qed.

  Goal forall t (rep1 rep2 : nat) , can_follow_hd (0 @ rep1 <~ inl read) [1 @ rep2 <~ inr read; t] -> False.
  Proof.
    intros.
    Fail elim_by_comm @H.
  Abort.

  Goal forall t (rep1 : nat) , can_follow_hd (1 @ rep1 <~ inl read) [0 @ I <~ inl (write 1); t] -> False.
  Proof.
    intros.
    Fail elim_by_comm @H.
  Abort.

  Ltac2 rec split_all_clauses (n : ident) :=
    let h := hyp n in
    lazy_match! type h with
    | ?a \/ ?b => destruct $h as [$n | $n] > [() | split_all_clauses n]
    | ?a /\ ?b =>
        let f1 := in_goal n in
        destruct $h as [$f1 $n];
        lazy_match! type (hyp f1) with
        | ?a = ?b => subst
        | _ => ()
        end;
        try (split_all_clauses n)
    | _ => ()
    end.

  (* Test: *)
  Goal True \/ True \/ True \/ True -> False.
  Proof.
    intros H.
    split_all_clauses @H > [() | () | () | ()].
  Abort.

  Goal forall a b, True /\ a = 1 /\ b = 2 /\ a = b -> False.
  Proof.
    intros a b H.
    split_all_clauses @H.
  Abort.

  Ltac2 simpl_par_cons_rep (n : ident) (g : ident) (te : ident) :=
    let rep := in_goal @rep in
    let h := hyp n in
    destruct $h as [$rep $n];
    let h := hyp n in
    let hte := in_goal @Hte in
    injection $h as $n $hte;
    subst $g;
    subst $te.

  (* Test: *)
  Goal forall g te,
      (exists rep : True, Some (g, te) = Some (1, 2)) ->
      g = 1 /\ te = 2.
  Proof.
    intros g te H.
    simpl_par_cons_rep @H @g @te.
    split; reflexivity.
  Qed.

  Ltac2 Type state := {comm_hyp : ident; te : ident; trace : ident}.

  Ltac2 gen_par_cons_unfold (t : ident) (n : ident) cont (s : 's) :=
    let g' := in_goal @g in
    let te := in_goal @te in
    let t' := in_goal @t' in
    let ht := in_goal @Ht in
    let htete' := in_goal @Htete' in
    let hg' := in_goal @Hg' in
    apply canned_par_opt_two in $n;
    let h := hyp n in
    destruct $h as [$g' [$te [$t' [$ht [$n [$htete' $hg']]]]]];
    subst $t;
    cbn in $n;
    split_all_clauses n >
      [simpl_par_cons_rep n g' te;
       cont te t' hg' htete' s..].

  Ltac2 perform_post_checks (s : state option) :=
    match s with
    | None => fail
    | Some s =>
        let ch := s.(comm_hyp) in
        elim_by_comm ch
    end.

  Ltac2 long_step (hypn : ident) : (ident * ident * ident) option :=
    let h := hyp hypn in
    cbn in $hypn;
    lazy_match! type h with
    | ReachableByTrace _ [] _ =>
        let s := in_goal @s in
        let hx := in_goal @Hx in
        let hy := in_goal @Hy in
        let hz := in_goal @Hz in
        inversion $h as [$s $hx $hy $hz | ];
        subst; clear $hypn;
        None
    | ReachableByTrace _ (_ :: _) _ =>
      let s' := in_goal @s in
      let te := in_goal @te in
      let tail := in_goal @tail in
      let hcr := in_goal @Hcr in
      let htl := in_goal @Htl in
      inversion_clear $h as [ |? $s' ? $te $tail $hcr $hypn];
      cbn in $hcr;
      Some (te, s', hcr)
    end.


  Ltac2 rec gen_par_unfold_ hook (te : ident) (t : ident) (n : ident) (hcomm : ident) (state : state option) :=
    first [ perform_post_checks state
          | hook () >
              [lazy_match! type (hyp n) with
               | GenEnsembleOpt {| processes := [] |} _ =>
                   apply canned_par_opt_nil in $n ; subst $t; hook ()
               | GenEnsembleOpt {| processes := ?pp |} _ =>
                   let state := Some {comm_hyp := hcomm; te := te; trace := t} in
                   gen_par_cons_unfold t n (gen_par_unfold_ hook) state
               end..]].

  Ltac2 gen_par_unfold (t : ident) (hyp_g : ident) hook :=
    gen_par_cons_unfold t hyp_g (gen_par_unfold_ hook) None.

  Goal forall n,
      -{{ fun s => stateG s var = n }}
         GenEnsembleOpt system
       {{ fun s => stateG s var = n + 2 }}.
  Proof with auto with slot.
    intros n t Hg [s_begin1 s_begin2] [s_end1 s_end2] Hrbt Hpre.
    unfold stateG in *. simpl in *.
    unfold Ensembles.In, system, of_progs in Hg.
    gen_par_unfold @t @Hg
      (fun _ => match long_step @Hrbt with
             | None => ()
             | Some (te, s, hcr) =>
                 destruct s;
                 unfold compose_state_transition in hcr;
                 (* printf "%t" (type (hyp hcr)); *)
                 (* ifcatch (fun () => split_all_clauses hcr) (fun _  => ()) (fun f => Message.print (Message.of_exn f)) *)
                 split_all_clauses hcr;
                 lazy_match! goal with
                 | [ h : mutex_state_transition _ _ _  |- _] =>
                     let h := hyp h in
                     inversion $h
                 end
             end).
    - ltac1:(lia).
    - ltac1:(lia).
  Qed.
End tests.
End Example.
