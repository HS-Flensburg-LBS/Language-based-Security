
(* Funktionen sind first-class values *)

(* Eigenschaften von Coq *)
(* statisches Typsystem *)
(* Typinferenz *)
(* Pattern Matching *)


Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.


Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.


Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).


Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.


Inductive bool : Type :=
| true : bool
| false : bool.


Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Example test_orb1 : (orb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb2 : (orb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb3 : (orb true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb4 : (orb false false) = false.
Proof.
  simpl.
  reflexivity.
Qed.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Example test_orb5 : false || false || true = true.
Proof.
  simpl.
  reflexivity.
Qed.


Check true.

Check (negb true).

Check negb.


Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Inductive color : Type :=
| black : color
| white : color
| primary : rgb -> color.


Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.


Module NatPlayground.

  (* Peano Zahlen *)

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Check O.
  Check (S O).
  Check (S (S O)).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S m => m
    end.

End NatPlayground.


Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S m) => m
  end.


Compute (minustwo 23).


Check S.

Check pred.

Check minustwo.


Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S m) => evenb m
  end.

Compute (evenb (S (S O))).
Compute (evenb O).


Module NatPlayground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  (* S n' <=match=> S (S O) *)
  (* => n' = S O *)

  (* Compute (plus (S (S O)) O). *)
  (* Compute (S (plus (S O) O)). *)
  (* Compute (S (S (plus O O))). *)

  (* (n' + 1) + m = n' + 1 + m = n' + m + 1 = (n' + m) + 1 *)

  Compute (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  (* Kommutativität *)
  (* Distributivität *)

  (* (n' + 1) * m = (n' * m) + m *)

  Fixpoint minus (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => match m with
              | O => n
              | S m' => minus n' m'
              end
    end.

  Fixpoint minus2 (n m : nat) : nat :=
    match (n, m) with
    | (O   , _   ) => O
    | (S _ , O   ) => n
    | (S n', S m') => minus2 n' m'
    end.

  (* (n' + 1) - (m ' + 1) = n' + 1 - m' - 1 = n' - m' *)

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Compute (exp (S (S O)) (S O)).
Compute (mult (S (S O)) (exp (S (S O)) O)).

  (* n^(p + 1) = n * n^p*)

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.


Compute (23 + 42 - 12).


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S _ => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint beq_nat2 (n m : nat) : bool :=
  match (n, m) with
  | (O, O) => true
  | (O, S _) => false
  | (S _, O) => false
  | (S n', S m') => beq_nat n' m'
  end.

(* n' + 1 = m' + 1 <=> n' = m' *)

(* less equal *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1 : (leb 2 2) = true.
Proof.
  simpl.
  reflexivity.
Qed.

(* Relation *)
(* Reflexivität *)
