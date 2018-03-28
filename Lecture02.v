

(* mehrstellige Funktionstypen *)

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


Check andb.


(* abstrakte Syntax *)

Inductive term : Type :=
| ttrue : term
| tfalse : term
| tzero : term
| tsucc : term -> term
| tpred : term -> term
| tiszero : term -> term
| tif : term -> term -> term -> term.


Definition example1 : term :=
  ttrue.

Definition example2 : term :=
  (tsucc tzero).

Definition example3 : term :=
  (tif tzero tfalse ttrue).

Definition example4 : term :=
  (tif (tif tzero ttrue (tsucc tfalse)) tfalse ttrue).


Compute example1.
Compute example2.
Compute example3.
Compute example4.


Fixpoint size (t : term) : nat :=
  match t with
  | ttrue => 1
  | tfalse => 1
  | tzero => 1
  | tsucc t1 => size t1 + 1
  | tpred t1 => size t1 + 1
  | tiszero t1 => size t1 + 1
  | tif t1 t2 t3 => size t1 + size t2 + size t3 + 1
  end.


Compute (size example1).
Compute (size example2).
Compute (size example3).
Compute (size example4).


Fixpoint depth (t : term) : nat :=
  match t with
  | ttrue => 1
  | tfalse => 1
  | tzero => 1
  | tsucc t1 => depth t1 + 1
  | tpred t1 => depth t1 + 1
  | tiszero t1 => depth t1 + 1
  | tif t1 t2 t3 =>
    max (max (depth t1) (depth t2)) (depth t3) + 1
  end.


Print example1.
Compute (depth example1).
Print example2.
Compute (depth example2).
Print example3.
Compute (depth example3).
Print example4.
Compute (depth example4).


(* Datei muss mit coqc kompiliert sein *)

Require Import Lecture01.


(* Proof by Simplification *)

Example test_orb : (orb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.


Theorem plus_0_n : forall n : nat, O + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


(* simpl, reflexivity, intros heißen Taktiken  *)

Theorem plus_0_n' : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n.
  (* simpl. *)
  reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


(* Proof by Rewriting *)

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  (* Alternative zum obigen Schritt, ersetzt in die andere Richtung *)
  (* rewrite <- H. *)
  reflexivity.
Qed.

Theorem mult_0_plus :
  forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n' m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.


(* Proof by Case Analysis *)

Theorem plus_1_neq_0 :
  forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  (* intros n. *)
  (* [| n'] heißt intro pattern *)
  (* destruct n as [| n']. *)
  (* alternativ  *)
  intros [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive :
  forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative :
  forall a b : bool, a && b = b && a.
Proof.
  intros a b.
  destruct a.
  (* a = true *)
  - destruct b.
    (* b = true *)
    + reflexivity.
    (* b = false *)
    + reflexivity.
  (* a = false *)
  - destruct b.
    (* b = true *)
    + reflexivity.
    (* b = false *)
    + reflexivity.
Qed.

Theorem andb_commutative' :
  forall a b : bool, a && b = b && a.
Proof.
  intros a b.
  destruct a, b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' :
  forall a b : bool, a && b = b && a.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(* Proof by Induction *)

(* - P 0 *)
(* - forall n' : nat, P n' -> P (S n') *)
(* -------------------- *)
(* forall n : nat, P n *)


(* IHn' : Induction Hypothesis n' *)

Theorem plus_n_0 :
  forall n : nat,
    n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* function application infix *)
(* f x + y = (f x) + y *)

Theorem minus_diag :
  forall n : nat,
    minus n n = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.    

Theorem plus_assoc' :
  forall a b c : nat,
    (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  - reflexivity.
  - simpl.
    rewrite -> IHa'.
    reflexivity.
Qed.

    (* S a' + b = S (a' + b) *)

    (* (S a' + b) + c = S (a' + b) + c = S ((a' + b) + c)  *)

    (* S a' + (b + c) = S (a' + (b + c)) *)
