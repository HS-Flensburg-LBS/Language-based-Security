(* Galina *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Inductive weekday : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday. *)

(* Aufzählungstyp / Enumeration *)

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

(* next_weekday(next_weekday(friday)) *)

Compute (next_weekday (next_weekday friday)).

Example test_next_weekday :
    (next_weekday (next_weekday friday)) = tuesday.
Proof.
    simpl.
    reflexivity.
Qed.


Inductive bool : Type :=
    | true
    | false.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Compute (negb false).

Example test_negb_false : (negb false) = true.
Proof.
    simpl.
    reflexivity.
Qed.


Definition andb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1 b2 : bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Example test_orb5 : false || false || true = true.
Proof.
    simpl.
    reflexivity.
Qed.


Check negb.


Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive color : Type :=
    | black
    | white
    (* | redGreen *)
    | primary (p : rgb).

(* color
black
white
primary red
primary green
primary blue
 *)

Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

(*
monochrome (primary red)

*)

Definition is_red (c : color) : bool :=
    match c with
    | primary red => true
    | _ => false
    end.


Module Playground.

    Definition b : rgb := blue.

End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.


Inductive bit : Type :=
 | B0
 | B1.

Inductive nybble : Type :=
 | bits (b0 : bit) (b1 : bit) (b2 : bit) (b3 : bit).

Check (bits B0 B1 B0 B0).


Definition not_all_zero (nb : nybble) : bool :=
    match nb with
    | bits B0 B0 B0 B0 => false
    | bits _ _ _ _ => true
    end.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

(*
0 = O
1 = S O
2 = S (S O)
3 = S (S (S O))
4 = S (S (S (S O)))
...
*)

Inductive nat' : Type :=
  | stop
  | tick (n : nat').


Definition pred (n : nat) : nat :=
    match n with
    | S m => m
    | O => O
    end.

Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S m) => even m
    end.

Compute (even (S (S (S O)))).

(*
even (S (S (S O)
  m = S O
even (S O)

*)

Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

(* plus (n' + 1) m = (plus n' m) + 1 *)

Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus (mult n' m) m
    end.


(* Example test_mult1 : (mult (S (S (S O))) (S (S (S O)))) = 9.
Proof.
    simpl.
    reflexivity.
Qed. *)

End NatPlayground.

(*
(n' + 1) * m = n' * m + m
*)


Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S _ => false
           end.
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.
