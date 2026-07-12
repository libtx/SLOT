From Ltac2 Require
  Fresh
  String
  Ident
  Std
  Ident
  Constr
  Control.
From Ltac2 Require Export
  Notations
  Printf
  Init.

From Hammer Require Import
  Tactics.

From SLOT Require Import
  TransitionSystem.

(* Alternative notation for inversion tactic that allows passing ident
as a destruction argument, which for some reason doesn't work for the
standard notation. *)
Ltac2 Notation "iinversion"
  arg(ident)
  pat(opt(seq("as", intropattern)))
  ids(opt(seq("in", list1(ident)))) :=
  Std.inversion Std.FullInversion (Std.ElimOnIdent arg) pat ids.

Ltac2 Notation "sauto" := ltac1:(sauto).

Ltac2 fresh_id str := Fresh.in_goal (Option.get (Ident.of_string str)).

Ltac2 ts_step h :=
  let hyp := Control.hyp h in
  match! Constr.type hyp with
   | TSMFunGen _ ?tr _ =>
       let s0 := fresh_id "s0_" in
       let s1 := fresh_id "s" in
       let s2 := fresh_id "s2_" in
       let trace := fresh_id "trace" in
       let event := fresh_id "event" in
       let h_rest := fresh_id "H" in
       let h_event := fresh_id (String.app "H" (Ident.to_string s1)) in
       let h_event_eq := fresh_id "H_e" in
       let h_trace_eq := fresh_id "H_tr" in
       let h_s2_eq := fresh_id "H_s2" in
       iinversion $h as [|$s0 $s1 $s2 $trace $event $h_rest $h_event $h_event_eq $h_trace_eq $h_s2_eq];
       try (subst $s2);
       try (subst $s0);
       clear $h; Std.rename [(h_rest, h)];
       match Constr.Unsafe.kind tr with
       | Constr.Unsafe.Var tr_id =>
           subst $tr_id
       | _ =>
           ()
       end
   end.

Ltac2 Notation "ts_step" id(ident) := ts_step id.
