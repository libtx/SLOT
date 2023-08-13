(** * SLOT model checker *)

From SLOT Require Export
     Foundations
     Generator
     Commutativity
     Handlers.

From Ltac2 Require Import Ltac2.
Import Ltac2.Notations Ltac2.Printf.
  (* Init List Ind Env Control Option Constr Std Array Notations Fresh Printf. *)

From Coq Require Import List Lia.
Import ListNotations.

Import better_parallel.

(** A tactic that tries to find a contradiction to [can_follow_hd] hypothesis named [hi].

 pid_compare_tact is a tactic that finds evidence that [pid1 > pid2]

 commut_tact is a tactic that finds evidence that trace elements commute. *)
Ltac2 elim_by_comm0 pid_compare_tact commut_tact (hi : ident) :=
  let hpid := Fresh.in_goal @Hpid in
  let hnoncomm := Fresh.in_goal @Hnoncomm in
  let hcomm := Fresh.in_goal @Hcomm in
  let h := Control.hyp hi in
  let try_find_comm () :=
    lazy_match! Constr.type (Control.hyp hnoncomm) with
    |  ~ events_commute ?a ?b => assert ($hcomm : events_commute $a $b) by commut_tact ()
    end;
    let h1 := Control.hyp hnoncomm in
    let h2 := Control.hyp hcomm in
    (destruct ($h1 $h2)) in
  destruct $h as [$hpid|$hnoncomm] > [solve [ pid_compare_tact () ] | solve [ try_find_comm () ]].

Ltac2 elim_by_comm hi := elim_by_comm0
                           (fun () => ltac1:(lia))
                           (fun () => (first [apply compose_comm | apply compose_comm_rev]))
                           hi.

From SLOT Require Import Deterministic Mutex.

Section tests.
  Import Var.
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
End tests.

(** Helper tactic to unfold nested [a /\ b /\ ...] or [a \/ b \/  ...] expressions *)
Ltac2 rec split_all_clauses (n : ident) :=
  let h := Control.hyp n in
  lazy_match! Constr.type h with
  | ?a \/ ?b => destruct $h as [$n | $n] > [() | split_all_clauses n]
  | ?a /\ ?b =>
      let f1 := Fresh.in_goal n in
      destruct $h as [$f1 $n];
      lazy_match! Constr.type (Control.hyp f1) with
      | ?a = ?b => subst
      | _ => ()
      end;
      try (split_all_clauses n)
  | _ => ()
  end.

Section tests.
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
End tests.

(** A helper tactic that simplifies the result of applying
[canned_par_opt_two] lemma to a generator: *)
Ltac2 simpl_par_cons_rep (n : ident) (g : ident) (te : ident) :=
  let rep := Fresh.in_goal @rep in
  let h := Control.hyp n in
  destruct $h as [$rep $n];
  let h := Control.hyp n in
  let hte := Fresh.in_goal @Hte in
  injection $h as $n $hte;
  subst $g;
  subst $te.

Section tests.
  Goal forall g te,
      (exists rep : True, Some (g, te) = Some (1, 2)) ->
      g = 1 /\ te = 2.
  Proof.
    intros g te H.
    simpl_par_cons_rep @H @g @te.
    split; reflexivity.
  Qed.
End tests.

Local Ltac2 Type state := {comm_hyp : ident; te : ident; trace : ident}.

Ltac2 perform_post_checks (s : state option) :=
  match s with
  | None => fail
  | Some s =>
      let ch := s.(comm_hyp) in
      elim_by_comm ch
  end.

Section canned_lemmas.
  Context `{Hhandler : IOHandler}.
  Let TE := ProcessEvent (IOp Request Reply).

  Lemma canned_par_opt_nil {last_pid}
    (t : list TE)
    (Hgen : GenEnsembleOpt {| last_pid := last_pid; processes := []|} t) :
    t = [].
  Proof.
    inversion Hgen.
    - reflexivity.
    - inversion H.
  Qed.

  Lemma canned_par_opt_cons {last_pid : PID}
    {p : @Runnable Request Reply}
    {rest : list (@Runnable Request Reply)}
    (t : list TE)
    (Hgen : GenEnsembleOpt {| last_pid := last_pid; processes := p :: rest|} t) :
    exists g' te t',
      t = te :: t' /\
        {| last_pid := last_pid; processes := p :: rest|} ~~> g' & te /\
        can_follow_hd te t' /\
        GenEnsembleOpt g' t'.
  Admitted.
End canned_lemmas.

Ltac2 gen_par_step (t : ident) (gen_hyp_n : ident) :=
  lazy_match! Constr.type (Control.hyp gen_hyp_n) with
  | @GenEnsembleOpt (@Parallel ?req_t ?rep_t) ?state_t ?event_t ?state_space_inst ?generator_inst {| processes := [] |} _ =>
      apply (@canned_par_opt_nil $req_t $rep_t) in $gen_hyp_n;
      subst $t;
      None
  |  @GenEnsembleOpt (@Parallel ?req_t ?rep_t) ?state_t ?event_t ?state_space_inst ?generator_inst {| processes := ?pp |} _ =>
      let g' := Fresh.in_goal @g in
      let te := Fresh.in_goal @te in
      let t' := Fresh.in_goal @t' in
      let ht := Fresh.in_goal @Ht in
      let hcomm := Fresh.in_goal @Htete' in
      let hg' := Fresh.in_goal @Hg' in
      apply (@canned_par_opt_cons $req_t $rep_t) in $gen_hyp_n;
      let h := Control.hyp gen_hyp_n in
      destruct $h as [$g' [$te [$t' [$ht [$gen_hyp_n [$hcomm $hg']]]]]];
      Some (g', te, t', ht, hcomm, hg')
  end.

Section tests.
  Let Handler := Var.t nat.
  Let Req := handler_request_t Handler.
  Let Rep := handler_reply_t Handler.

  Goal forall t, GenEnsembleOpt (of_progs []) t -> t = [].
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_step @t @Hg.
    reflexivity.
  Qed.

  Goal forall t, GenEnsembleOpt (of_progs [done Var.write 1]) t -> False.
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_step @t @Hg > [()].
  Abort.

  Goal forall t, GenEnsembleOpt (of_progs [done Var.write 1; done Var.write 2]) t -> False.
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_step @t @Hg > [()].
  Abort.
End tests.

Ltac2 rec gen_par_unfold0 (t : ident) (gen_hyp_n : ident) (state : state option) hook :=
  orelse
    (fun () => perform_post_checks state)
    (fun _ =>
       Option.may hook state >
         [match gen_par_step t gen_hyp_n with
          | None =>
              Option.may hook state
          | Some (g', te, t', ht, hcomm, hg') =>
              (* subst $t; *)
              cbn in $gen_hyp_n;
              let state := Some {comm_hyp := hcomm; te := te; trace := t} in
              split_all_clauses gen_hyp_n >
                [simpl_par_cons_rep gen_hyp_n g' te;
                 gen_par_unfold0 t' hg' state hook..]
          end..]).

Ltac2 gen_par_unfold (t : ident) (hyp_g : ident) hook :=
  gen_par_unfold0 t hyp_g None hook.

Section tests.
  Let Handler := Var.t nat.
  Let Req := handler_request_t Handler.
  Let Rep := handler_reply_t Handler.

  Goal forall t, GenEnsembleOpt (of_progs []) t -> t = [].
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_unfold @t @Hg (fun _ => ()).
    reflexivity.
  Qed.

  Goal forall t, GenEnsembleOpt (of_progs [done (Var.write 1)]) t -> t = [0 @ I <~ Var.write 1].
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_unfold @t @Hg (fun _ => ()).
    destruct rep.
    apply Ht.
  Qed.

  Goal forall t, GenEnsembleOpt (of_progs [done (Var.write 1); done (Var.write 2)]) t ->
            t = [0 @ I <~ Var.write 1; 1 @ I <~ Var.write 2] \/
              t = [1 @ I <~ Var.write 2; 0 @ I <~ Var.write 1].
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_unfold @t @Hg (fun _ => ());
      destruct rep; destruct rep0; subst.
    - left. reflexivity.
    - right. reflexivity.
  Qed.

  Goal forall t, GenEnsembleOpt (of_progs [do _ <- (Var.write 1); done (Var.write 2)]) t ->
            t = [0 @ I <~ Var.write 1; 0 @ I <~ Var.write 2].
  Proof.
    intros t Hg.
    unfold of_progs in Hg.
    gen_par_unfold @t @Hg (fun _ => ());
      destruct rep; destruct rep0; subst.
    - reflexivity.
  Qed.

  Let prog : @Program Req Rep :=
        do n <- Var.read;
        done Var.write (n + 1).

  Let system := of_progs [prog; prog].

  Goal forall t, GenEnsembleOpt system t -> False.
  Proof.
    intros t Hg.
    unfold system, of_progs, prog in Hg.
    gen_par_unfold @t @Hg (fun s => ()) > [() | () | () | () | () | ()].
  Abort.
End tests.

Ltac2 handler_step (hypn : ident) : (ident * ident * ident) option :=
  let h := Control.hyp hypn in
  cbn in $hypn;
  lazy_match! Constr.type h with
  | ReachableByTrace _ [] _ =>
      let s := Fresh.in_goal @s in
      let hx := Fresh.in_goal @Hx in
      let hy := Fresh.in_goal @Hy in
      let hz := Fresh.in_goal @Hz in
      inversion $h as [$s $hx $hy $hz | ];
      subst; clear $hypn;
      None
  | ReachableByTrace _ (_ :: _) _ =>
      let s' := Fresh.in_goal @s in
      let te := Fresh.in_goal @te in
      let tail := Fresh.in_goal @tail in
      let hcr := Fresh.in_goal @Hcr in
      let htl := Fresh.in_goal @Htl in
      inversion_clear $h as [ |? $s' ? $te $tail $hcr $hypn];
      cbn in $hcr;
      Some (te, s', hcr)
  end.

Module Example.
  Import Handlers.Deterministic Handlers.Deterministic.Var.

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

  Goal forall n,
      -{{ fun s => stateG s var = n }}
         GenEnsembleOpt system
       {{ fun s => stateG s var = n + 2 }}.
  Proof with auto with slot.
    intros n t Hg [s_begin1 s_begin2] [s_end1 s_end2] Hrbt Hpre.
    unfold stateG in *. simpl in *.
    unfold Ensembles.In, system, of_progs, prog in Hg.
    Set Ltac2 Backtrace.
    gen_par_unfold @t @Hg (fun _ => ()).

      (fun _ => match handler_step @Hrbt with
             | None => ()
             | Some (te, s, hcr) =>
                 destruct s;
                 unfold compose_state_transition in hcr;
                 (* printf "%t" (type (hyp hcr)); *)
                 (* ifcatch (fun () => split_all_clauses hcr) (fun _  => ()) (fun f => Message.print (Message.of_exn f)) *)
                 split_all_clauses hcr;
                 lazy_match! goal with
                 | [ h : mutex_state_transition _ _ _  |- _] =>
                     let h := Control.hyp h in
                     inversion $h
                 end
             end).
    - ltac1:(lia).
    - ltac1:(lia).
  Qed.
End Example.
