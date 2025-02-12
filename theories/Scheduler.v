From Coq Require Import
  ZArith
  List
  String
  SetoidClass.

Import ListNotations.
Open Scope positive_scope.

From SLOT Require Import
  Trace.

From Hammer Require Import
  Tactics.

Definition PID := list positive.

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
     right associativity) : slot_scope.

Notation "'spawn' V '<-' I ; C" := (p_spawn (I) (fun V => C))
    (at level 100, C at next level, V ident,
     right associativity) : slot_scope.
(* end details *)

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
        h_state_setoid :: Setoid h_state;
      }.

  Global Instance ioHandlerTransitionSystem `(IOHandler) : @TransitionSystem h_state (IOp Request Reply) True :=
    {
      future s f :=
        match f with
        | fut_result _ => False
        | fut_cont l s' => h_state_transition s l s'
        end;
      state_setoid := h_state_setoid
    }.
End iodefs.

Section naive_scheduler.
  (* Scheduler is simply a list of trace elements, together with their
  futures, in order that represents future execution: *)
  Context `{IOH : IOHandler}.
  Let Prog := @Program Request Reply.

  Inductive TraceEvent :=
  | te_spawn : forall (pid : PID) (new_thread : Prog), TraceEvent
  | te_exit : forall (pid : PID) (result : ProgramReturn), TraceEvent
  | te_iop : IOp Request Reply -> TraceEvent.

  Record Task :=
    { pid : PID;
      nextchild : positive;
    }.

  Inductive Task' : TraceEvent -> Task -> NewTasks -> Prop :=
  | task'exit : forall pid result task,
      Task'
        (te_exit pid result)
        task
        newtasks₀
  | task'spawn : forall pid nc cont new,
      let newpid := pid ++ [nc] in
      Task'
        (te_spawn newpid new)
        {| pid := pid; nextchild := nc; cont := cont |}
        newtasks₂ {| pid := pid; nextchild := nc |} {| pid := newpid; nextchild := new |}.


  | thread'exit : forall pid next result,
      Thread'
        {| pid := pid; nextchild := next; prog := p_dead result |}
        (te_exit pid result)
        []
  | thread'spawn : forall pid next new cont,
      let newpid := pid ++ [next] in
      Thread'
        {| pid := pid; nextchild := next; prog := p_spawn new cont |}
        (te_spawn newpid new)
        [{| pid := pid; nextchild := Pos.succ next; prog := cont newpid |};
         {| pid := newpid; nextchild := 1; prog := new |}].

  Inductive Scheduler := sched : list Thread -> Scheduler.

  Inductive schedule : Thread -> list Thread -> list Thread -> Prop :=
  | schedule₁ : forall t l,
      schedule t l (t :: l)
  | schedule₂ : forall t a l l',
      schedule t l l' ->
      schedule t (a :: l) l'.
End naive_scheduler.
(* Section trie. *)
(*   Context `{IOH : IOHandler}. *)

(*   Let Prog := @Program Request Reply. *)

(*   Inductive TraceEvent := *)
(*   | te_spawn : forall (pid : PID) (new_thread : Prog), TraceEvent *)
(*   | te_exit : forall (pid : PID) (result : ProgramReturn), TraceEvent *)
(*   | te_iop : IOp Request Reply -> TraceEvent. *)

(*   Definition lift_pid (cid : positive) (te : TraceEvent) : TraceEvent := *)
(*       match te with *)
(*       | te_spawn pid new => *)
(*           te_spawn (cid :: pid) new *)
(*       | te_exit pid result => *)
(*           te_exit (cid :: pid) result *)
(*       | te_iop {| iop_pid := pid; iop_req := req; iop_rep := rep |} => *)
(*           te_iop {| iop_pid := cid :: pid; iop_req := req; iop_rep := rep |} *)
(*       end. *)

(*   Inductive Scheduler := *)
(*   | sched₀ : forall (parent : positive) (children : @Σ Scheduler TraceEvent), *)
(*       Scheduler *)
(*   | sched₁ : forall (parent : positive) (nextpid : positive) (this : Prog) (children : @Σ Scheduler TraceEvent), *)
(*       Scheduler. *)

(*   Check @future. *)
(*   Check @Σfuture. *)

(*   Inductive Scheduler' : Scheduler -> @Future Scheduler TraceEvent True -> Prop := *)
(*   | sched'₀ : forall parent σ σ' te, *)
(*       let TS := {| future := Scheduler' |} in *)
(*       let TS' := {| future := @Σfuture _ _ _ TS |} in *)
(*       @future _ _ _ TS' σ ~[te]~> σ' -> *)
(*       Scheduler' (sched₀ parent σ) ~[lift_pid parent te]~> (sched₀ parent σ'). *)


(* forall npid new cont σ, *)
(*       sched (npid ( *)

(*   Inductive TrieStep : TrieNode -> @Future TrieNode Label True -> Prop := *)
(*   | tstep_current : forall node fut, *)
(*       mutation node fut -> *)
(*       TrieStep node fut. *)
(*   | tstep_child : forall this cid child child' rest label, *)
(*       TrieStep child ~[label]~> child' -> *)
(*       TrieStep *)
(*         (trie_node this ((cid, child) :: rest)) ~[lift cid label]~> *)
(*         (trie_node this ((cid, child') :: rest)) *)
(*   | tstep_next_child : forall this skip rest fut, *)
(*       TrieStep (trie_node this rest) fut -> *)
(*       TrieStep (trie_node this (skip :: rest)) fut *)
(*   | tstep_rem_child : forall this cid dead rest fut, *)
(*       TrieStep dead ~>[I] -> *)
(*       TrieStep (trie_node this ((cid, dead) :: rest)) fut -> *)
(*       TrieStep (trie_node this rest) fut. *)
(* End trie. *)

(* Section scheduler. *)
(*   Context {Request : Type} {Reply : Request -> Type}. *)

(*   Record SchedulerNodeS := *)
(*     { nextchild : positive; *)
(*       this_thread : option Prog *)
(*     }. *)

(*   Definition SchedulerS : Type := @TrieNode SchedulerNodeS. *)

(*   Definition sched_node_step (s : SchedulerS) (fut : @Future SchedulerS TraceEvent True) : Prop := *)
(*     match s with *)
(*       trie_node {| nextchild := next; this_thread := prog |} children => *)
(*         match prog with *)
(*         | None => *)
(*             match children with *)
(*             | [] => *)
(*                 fut = fut_result I *)
(*             | _ => *)
(*                 False *)
(*             end *)
(*         | Some prog => *)
(*             match prog with *)
(*             | p_dead ret => *)
(*                 let te := te_exit [] ret in *)
(*                 let this' := {| nextchild := next; this_thread := None |} in *)
(*                 fut = fut_cont te (trie_node this' children) *)
(*             | p_cont req cont => *)
(*                 exists rep, *)
(*                 let te := te_iop {| iop_pid := []; iop_req := req; iop_rep := rep |} in *)
(*                 let this' := {| nextchild := next; this_thread := Some (cont rep) |} in *)
(*                 fut = fut_cont te (trie_node this' children) *)
(*             | p_spawn new cont => *)
(*                 let pid := [next] in *)
(*                 let te := te_spawn pid new in *)
(*                 let this' := {| nextchild := Pos.succ next; this_thread := Some (cont pid) |} in *)
(*                 let newchild := trie_node {| nextchild := 1; this_thread := Some new |} [] in *)
(*                 let children' := (next, newchild) :: children in *)
(*                 fut = fut_cont te (trie_node this' children') *)
(*             end *)
(*         end *)
(*     end. *)

(*   Definition lift_pid (cid : positive) (te : TraceEvent) : TraceEvent := *)
(*       match te with *)
(*       | te_spawn pid new => *)
(*           te_spawn (cid :: pid) new *)
(*       | te_exit pid result => *)
(*           te_exit (cid :: pid) result *)
(*       | te_iop {| iop_pid := pid; iop_req := req; iop_rep := rep |} => *)
(*           te_iop {| iop_pid := cid :: pid; iop_req := req; iop_rep := rep |} *)
(*       end. *)


(*   Global Instance schedulerTS : @TransitionSystem SchedulerS TraceEvent True := *)
(*     { *)
(*       future := TrieStep sched_node_step lift_pid *)
(*     }. *)
(* End scheduler. *)

(* Section scheduler_tests. *)
(*   Let Req := positive. *)
(*   Let Rep (_ : Req) := True. *)

(*   Let complete := trie_node {| nextchild := 1; this_thread := None |} []. *)
(*   Let sys1 := trie_node {| nextchild := 1; this_thread := Some (@p_dead _ Rep normal) |} []. *)

(*   Ltac inv A := inversion A; subst; clear A. *)

(*   Goal forall t, Trace _ sys1 (trie_node ) t -> *)
(*                  t = [te_exit [] normal]. *)
(*   Proof. *)
(*     intros. *)
(*     inv H. cbn in H0. inv H0. *)
(*     2:{ inversion_clear H6. } *)
(*     2:{ inversion_clear H4. } *)
(*     inv H2. subst pid s'. *)
(*     inv H1. *)
(*     cbn in H. *)

(*     inversion H3; subst. subst pid s0 s1 s2 s'. *)
(*     inversion H1; subst. *)



(*     inversion_clear H0. *)
(*     - inversion_clear H. *)
(*       subst pid s0 s1 s2. *)
(*       inversion_clear H1. *)
(*       + reflexivity. *)
(*       + inversion_clear H. *)
