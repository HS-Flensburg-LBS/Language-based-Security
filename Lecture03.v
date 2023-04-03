
(* Simplification *)
(* Taktiken: simpl *)

(* Rewriting *)
(* Taktiken: rewrite *)

(* Case Analysis *)
(* Taktiken: destruct *)

(* Taktiken
- simpl
- rewrite
- destruct
- reflexivity
- unfold
- intros
*)

(* Funktionen/Methoden *)

(*
Fixpoint add (m n : nat) :=
    match m with
    |
    end.

add m n
-> unfold
match m with
| ...
end.
*)

(* match common_denum .. with *)

(*
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
*)

(* Induktion

P(0)
forall n:nat, P(n) -> P(n + 1)
*)

(* Set Printing Parentheses. *)

Theorem add_O_r : forall n : nat, n + O = n.
Proof.
    intros n.
    (* destruct n as [| n']. *)
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

(*
Fall n = 1:

IHn': (O - O) = 0
---------------------
((S O) - (S O)) = 0

Fall n = 2:

IHn': (1 - 1) = 0
---------------------
((S 1) - (S 1)) = 0

...
*)

(* Lemma *)

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.


(* Listen *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).


Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.


Definition mylist :=
    1 :: (2 :: (3 :: [])).


Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => []
    | S count' => n :: (repeat n count')
    end.

Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | cons h t => S (length t)
    end.

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
    end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | cons h t => h
    end.

Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | cons h t => t
    end.

Theorem nil_app: forall l : natlist, [] ++ l = l.
Proof.
    intros l.
    (* ([ ] ++ l) = app nil l *)
    (* simpl. *)
    reflexivity.
Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
    intros l.
    destruct l as [| n l'].
    - reflexivity.
    - reflexivity.
Qed.

(* Unset Printing Notations. *)
Set Printing Parentheses.

Theorem app_assoc: forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - (*
    (n :: l1') ++ l2
    =
    app (cons n l1') l2
    =
    cons n (app l1' l2)
    =
    n :: (l1' ++ l2)
    *)
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Inductive infinite : Type :=
  | More (i : infinite).
