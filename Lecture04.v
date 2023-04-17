
(* Polymorphismus/Generics *)

(* Polymorphe Listen *)

Inductive list (A : Type) : Type :=
  | nil
  | cons (n : A) (l : list A).

Arguments nil {A}.
Arguments cons {A}.


Check list.

(* list ist ein Typkonstruktor *)


Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(* type holes *)

(* Implizite Parameter *)

Fixpoint repeat {A : Type} (a : A) (count : nat) : list A :=
    match count with
    | O => nil
    | S count' => cons a (repeat a count')
    end.

Definition list1 : list bool :=
  cons false nil.


Fixpoint length {A : Type} (l : list A) : nat :=
    match l with
    | nil => O
    | cons h t => S (length t)
    end.

Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
    end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Definition hd {A : Type} (default : A) (l : list A) : A :=
    match l with
    | nil => default
    | cons h t => h
    end.

Definition tl {A : Type} (l : list A) : list A :=
    match l with
    | nil => @nil A
    | cons h t => t
    end.


(* Maybe/Optional/Option *)

Inductive option {A : Type} : Type :=
  | None
  | Some (x : A).


(* Higher-order Functions *)

Definition doit3times (A : Type) (f : A -> A) (n : A) : A :=
  f (f (f n)).

Fixpoint filter {A : Type} (pred : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => if pred h
              then h :: filter pred t
              else filter pred t
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Example test_filter1 :
  filter even (1 :: 2 :: 3 :: 4 :: []) = (2 :: 4 :: []).
Proof.
  reflexivity.
Qed.


(* Anonyme Funktionen/Lambda-Funktionen *)

(*
- Formale Grundlage für imperative Sprachen sind die Turing-Maschinen
- Formale Grundlage für funktionale Sprachen ist der Lambda-Kalkül
*)

Example test_anon_fun :
  doit3times _ (fun n => n * n) 2 = 256.
Proof.
  reflexivity.
Qed.


Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | h :: t => f h :: map f t
  end.


(* Neue Taktiken *)

(* apply *)

Theorem silly1 : forall (n m : nat),
  n = m -> n = m.
Proof.
  intros n m H.
  apply H.
Qed.


Theorem silly2 : forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p H1 H2.
  apply H2.
  apply H1.
Qed.


Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m H1 H2.
  apply H2.
  apply H1.
Qed.


(* apply with *)

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.


Theorem trans_eq : forall (A : Type) (n m o : A),
  n = m -> m = o -> n = o.
Proof.
  intros A n m o H1 H2.
  rewrite H1.
  apply H2.
Qed.


Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply trans_eq with (m := [c; d]).
  - apply H1.
  - apply H2.
Qed.

Check trans_eq.
