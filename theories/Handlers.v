(* SLOT, a formally verified model checker
   Copyright (C) 2019-2023  k32

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

(** * Combination of two handlers *)

From Hammer Require Import
     Tactics.

From SLOT Require Import
     Foundations
     Commutativity
     Tactics.

(** * Helper functions for getting request and result types of the handler *)
Definition handler_request_t {Req Ret} `(_ : @IOHandler Req Ret) : Type := Req.
Definition handler_reply_t {Req Ret} `(_ : @IOHandler Req Ret) : Req -> Type := Ret.

Section ComposeHandlers.
  Context {Request__l Request__r Reply__l Reply__r}
          (h_l : @IOHandler Request__l Reply__l)
          (h_r : @IOHandler Request__r Reply__r).

  Let S_l := @h_state _ _ h_l.
  Let S_r := @h_state _ _ h_r.

  Definition compose_state : Type := S_l * S_r.
  Let S := compose_state.

  Definition compose_request : Type := Request__l + Request__r.

  Definition compose_reply (request : compose_request) :=
    match request with
    | inl l => Reply__l l
    | inr r => Reply__r r
    end.

  Let TE := TraceElem compose_request compose_reply.

  Definition compose_state_transition (s : S) (te : TE) (s' : S) : Prop.
    destruct s as [l r]. destruct s' as [l' r'].
    destruct te as [pid [req ret]].
    destruct req as [req|req].
    - exact (r = r' /\ h_state_transition l (pid @ ret <~ req) l').
    - exact (l = l' /\ h_state_transition r (pid @ ret <~ req) r').
  Defined.

  Global Instance compose : @IOHandler compose_request compose_reply :=
    {| h_state            := compose_state;
       h_state_transition := compose_state_transition;
    |}.

  Definition te_subset_l (te : TE) :=
    match te with
    | {| te_event := {| iop_req := inl _ |} |} => True
    | _ => False
    end.

  Definition te_subset_r (te : TE) :=
    match te with
    | {| te_event := {| iop_req := inr _ |} |} => True
    | _ => False
    end.

  Lemma compose_comm pid1 pid2 req1 req2 ret1 ret2 :
      events_commute (pid1 @ ret1 <~ inl req1)
                     (pid2 @ ret2 <~ inr req2).
  Proof with firstorder; auto with slot.
    intros [s_l s_r] [s_l' s_r'].
    split; intros H;
      unfold_trace H (fun st _ Hcr => destruct st; unfold compose_state_transition in Hcr);
      firstorder;
      subst;
      simpl in *.
    - forward (s_l, s_r')...
      forward (s_l', s_r')...
    - forward (s_l', s_r)...
      forward (s_l', s_r')...
  Qed.

  Definition lift_l (prop : S_l -> Prop) : compose_state -> Prop :=
    fun s => match s with
            (s_l, _) => prop s_l
          end.

  Definition lift_r (prop : S_r -> Prop) : compose_state -> Prop :=
    fun s => match s with
            (_, s_r) => prop s_r
          end.
End ComposeHandlers.

Infix "<+>" := (compose)(at level 100).

Ltac decompose_state :=
  repeat match goal with
           [H : compose_state _ _ |- _ ] =>
           let l := fresh "s_l" in
           let r := fresh "s_r" in
           destruct H as [l r]; simpl in l,r
         end.

#[export] Hint Transparent compose_state : slot.

From Ltac2 Require Init List Ind Env Control Option Constr Std Array Notations.

Import Init Std Control.

Ltac2 Type Handlers := unit -> constr list.

(* Generate a composite handler class *)
Ltac2 makeClass (handlers : Handlers) :=
  let composeClasses := (fun acc class => constr:(compose $acc $class)) in
  let term :=
    match handlers () with
    | class :: rest => List.fold_left composeClasses rest class
    | []           => Control.throw No_value
    end in
  Control.refine (fun () => term).

Import Constr.Unsafe.

Ltac2 indRef (ind : constr) : inductive :=
  match kind ind with
  | Ind ind _ => ind
  | _         => throw_invalid_argument "Argument must be an instance of an inductive type"
  end.

(* Emit AST that performs case analysis of term [what2match] of inductive type [indt] *)
Ltac2 makeCase (return_type : constr) (what2match : constr) (indt : constr) (f : inductive -> int -> constr) :=
  let indref := indRef indt in
  let type := '(fun _ : $indt => $return_type) in
  let d := Ind.data indref in
  let n := Ind.nconstructors d in
  let branches := Array.init n (f indref) in
  make (Case (case indref) type NoInvert what2match branches).

Import Ltac2.Notations.

(* Return AST corresponding to the request type of i-th handler: *)
Ltac2 requestType (hh : Handlers) (id : int) :=
  let hh := hh () in
  let class := List.nth hh id in
  lazy_match! Constr.type class with
  | @IOHandler ?req ?rep => req
  end.

Ltac2 makeRequestTypeAst (hh : Handlers) (indt : constr) : constr :=
  let binder := Constr.Binder.make (Some @a) indt in
  let what2match := make (Rel 1) in
  make (Lambda binder (makeCase 'Type what2match indt (fun _ => requestType hh))).

Ltac2 makeRequestType (hh : Handlers) (indt : constr) :=
  Control.refine (fun () => makeRequestTypeAst hh indt).

Ltac2 constructor2constr (d : Ind.data) (i : int) : constr :=
  let c := Ind.get_constructor d i in
  let c := Std.ConstructRef c in
  Env.instantiate c.

Ltac2 compositeReqConstr (type : constr) (n : int) (i : int) :=
  let inl a := make (App 'inl (Array.of_list [a])) in
  let inr a := make (App 'inr (Array.of_list [a])) in
  let rec iter acc a :=
    match Int.gt a 0 with
    | true => iter (inl acc) (Int.sub a 1)
    | false => acc
    end in
  let (inner, n) := match i with
                    | 0 => inl (make (Rel 1)), Int.sub n 2
                    | _ => inr (make (Rel 1)), Int.sub n 1
                    end in
  let ast := iter inner (Int.sub n i) in
  let binder := Constr.Binder.make (Some @req) type in
  make (Lambda binder ast).

Ltac2 makeReqAst (hh : Handlers) (ind : constr) (reqT : constr) (class : constr) :=
  let indref := indRef ind in
  let n := Ind.nconstructors (Ind.data indref) in
  let outer_binder := Constr.Binder.make (Some @id) ind in
  let return_type := lazy_match! Constr.type class with
                     | @IOHandler ?req _ => req
                     end in
  let id := make (Rel 1) in
  let outer_type := make (Prod (Constr.Binder.make None (make (App reqT (Array.of_list [id])))) return_type) in
  let ast := makeCase outer_type id ind (fun d i =>
                                            let constr := (constructor2constr (Ind.data d) i) in
                                            let type := '($reqT $constr) in
                                            compositeReqConstr type n i) in
  make (Lambda outer_binder ast).

Ltac2 makeReq hh ind reqT class := Control.refine (fun () => makeReqAst hh ind reqT class).

From SLOT Require Deterministic.

Section test.
  Import Deterministic.

  Inductive handlerId := var | self | log | var2.
  Ltac2 handlerSpec () := ['(Var.t bool); 'Self.t; '(Log.t nat); '(Var.t nat)].

  Definition handler := ltac2:(makeClass handlerSpec).

  Definition reqT := ltac2:(makeRequestType handlerSpec 'handlerId).

  Definition req := ltac2:(makeReq handlerSpec 'handlerId 'reqT 'handler).

  Eval cbv in req var2 (Var.read).
End test.
