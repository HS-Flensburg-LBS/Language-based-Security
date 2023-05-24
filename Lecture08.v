Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.Pnat.
Require Import Coq.Lists.List.
Import ListNotations.

(* Inductively Defined Propositions *)

(* Collatz-Vermutung *)

Fixpoint div2 (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 0
    | S (S n) => S (div2 n)
    end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition f (n : nat) : nat :=
    if even n then div2 n
    else (3 * n) + 1.

(* 12, 6, 3, 10, 5, 16, 8, 4, 2, 1
19, 58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1. *)

Fail Fixpoint reaches_1_in (n : nat) : nat :=
    if n =? 1 then 0
    else 1 + reaches_1_in (f n).


Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

Lemma collatz : forall n : nat, reaches_1 n.
Admitted.


(* Definition Even (n : nat) : Prop :=
    exists k : nat, n = double k

even n = true *)


(* Inductive list (A : Type) : Type :=
    | nil                       : list A
    | cons (x : A) (l : list A) : list A. *)


(* Lemma ev_SS: forall n : nat, ev n -> ev (S (S n)) *)

(*
ev (S (S (S (S 0))))
ev (S (S n))
n := (S (S 0))
*)


Inductive ev : nat -> Prop :=
    | ev_0 : ev 0
    | ev_SS (n : nat) (H : ev n) : ev (S (S n)).


Theorem ev_4 : ev 4.
Proof.
    apply ev_SS.
    apply ev_SS.
    apply ev_0.
Qed.

Theorem ev_4' : ev 4.
Proof.
    apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(*
ev (4 + n)
ev (S (S (S (S n))))
*)


Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
    intros n H.
    (* apply ev_SS.
    apply ev_SS.
    apply H. *)
    apply (ev_SS _ (ev_SS _ H)).
Qed.


Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
    intros n E.
    destruct E as [| n' E'].
    - left.
      reflexivity.
    - right.
      exists n'.
      split.
      + reflexivity.
      + apply E'.
Qed.

(*
S (S n) = S (S n')
->
n = n'
*)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
    intros n H.
    apply ev_inversion in H.
    destruct H as [H1|H2].
    - discriminate H1.
    - destruct H2 as [n' [Hn' Hevn']].
      injection Hn' as Heq.
      rewrite Heq.
      apply Hevn'.
Qed.


Theorem evSS_ev' : forall n, ev (S (S n)) -> ev n.
Proof.
    intros n H.
    inversion H as [| n' E' Heq].
    apply E'.
Qed.


Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
    intros n m o H.
    injection H as H1 H2.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Theorem inversion_ex1' : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
    intros n m o H.
    inversion H.
    reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
    intros n H.
    discriminate H.
Qed.

Theorem inversion_ex2' : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
    intros n H.
    inversion H.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition Even x := exists n : nat, x = double n.

Lemma ev_Even : forall (n : nat),
  ev n -> Even n.
Proof.
    intros n E.
    induction E as [| n' E' IH].
    - exists 0.
      reflexivity.
    - unfold Even in *.
      destruct IH as [k Hk].
      exists (S k).
      simpl.
      do 2 f_equal.
      apply Hk.
Qed.


Module Playground.

(* ev n  *)

(* Relationen *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

(* Notation "n <= m" := (le n m). *)


(* n <= n *)
(* n <= m  ->  n <= m + 1 *)

Theorem test_le1 :
  le 3 3.
Proof.
    apply (le_n 3).
Qed.

Theorem test_le2 :
  le 3 6.
Proof.
    apply le_S.
    apply le_S.
    apply le_S.
    apply le_n.
Qed.

(*

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

*)

(*
Lemma le_n: forall n : nat, le n n

Lemma le_S: forall n m : nat, le n m -> le n (S m)
*)

Theorem test_le2' :
  le 3 6.
Proof.
    apply (le_S 3 5 (le_S 3 4 (le_S 3 3 (le_n 3)))).
Qed.

Theorem test_le3 :
  (le 2 1) -> 2 + 2 = 5.
Proof.
    intros H.
    inversion H.
    inversion H2.
Qed.
