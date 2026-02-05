From Coq Require Import
  List
  SetoidClass.

From Hammer Require Import
  Tactics.

Import ListNotations.

Section defn.
  Context {T : Type}.

  Record Queue :=
    { front :: list T;
      back :: list T;
    }.

  Definition to_list (q : Queue) : list T :=
    let (f, b) := q in
    f ++ rev b.

  Definition push (t : T) (q : Queue) : Queue :=
    let (f, b) := q in
    {| front := t :: f; back := b |}.

  Definition pop (q : Queue) : option T * Queue :=
    let (f, b) := q in
    match b with
    | e :: b =>
        (Some e, {| front := f; back := b |})
    | [] =>
        let b := rev f in
        match b with
        | e :: b =>
            (Some e, {| front := []; back := b |})
        | [] =>
            (None, q)
        end
    end.

  Global Program Instance queueSetoid : Setoid Queue :=
    { equiv a b :=
        to_list a = to_list b
    }.
  Next Obligation.
    split.
    - sauto.
    - sauto.
    - intros a b c Hab Hbc.
      sauto unfold: to_list.
  Qed.
End defn.
