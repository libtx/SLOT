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
    - refine (r = r' /\ h_state_transition l (pid @ ret <~ req) l').
    - refine (l = l' /\ h_state_transition r (pid @ ret <~ req) r').
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

(** Warning: [lift] tactic will emit arbitrary results when there are
multiple handlers of the same type combined, so avoid using it this
way *)
Ltac lift X :=
 match goal with
   |- ?top =>
   match eval cbv in top with
   | _ => exact X
   | (?a + ?b)%type =>
     (apply (@inl a b) + apply (@inr a b)); lift X
   end
 end.

Ltac decompose_state :=
  repeat match goal with
           [H : compose_state _ _ |- _ ] =>
           let l := fresh "s_l" in
           let r := fresh "s_r" in
           destruct H as [l r]; simpl in l,r
         end.

#[export] Hint Transparent compose_state : slot.
