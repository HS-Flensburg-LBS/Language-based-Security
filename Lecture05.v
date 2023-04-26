Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.Pnat.


(*
1 + 2 = 2 + 1

forall m n, ... -> m + n = n + m
*)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(* Inductive ratlist : Type :=
  | nil
  | cons (r : rat) (l : ratlist). *)

(* freie Theoreme *)

(* CompCert *)

(* injection *)

(* Inductive nat : Type :=
  | O
  | S (n : nat). *)

Theorem S_injective : forall (n m :nat),
  S n = S m -> n = m.
Proof.
    intros n m H1.
    assert (H2: n = pred (S n)).
    - reflexivity.
    - rewrite H2.
      rewrite H1.
      reflexivity.
Qed.

Theorem S_injective' : forall (n m :nat),
  S n = S m -> n = m.
Proof.
    intros n m H.
    injection H as Hnm.
    apply Hnm.
Qed.

Theorem injection_ex: forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof.
    intros n m o H.
    injection H as H1 H2.
    rewrite H1.
    symmetry.
    apply H2.
Qed.


Theorem discriminate_ex1: forall (n m : nat),
    false = true -> n = m.
Proof.
    intros n m H.
    discriminate H.
Qed.

(* principle of explosion *)

(* ex falso quodlibet *)

Theorem discriminate_ex2: forall (n : nat),
    S n = O -> 2 + 2 = 5.
Proof.
    intros n H.
    discriminate H.
Qed.

Theorem eqb_0_l: forall (n : nat),
  0 =? n = true -> n = 0.
Proof.
    intros n.
    destruct n as [| n'] eqn:E.
    - reflexivity.
    (* - simpl in H. *)
    - simpl.
      intros H.
      discriminate H.
Qed.

Theorem f_equal: forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
    intros A B f x y H.
    rewrite H.
    reflexivity.
Qed.

Theorem eq_implies_succ_equal: forall (n m : nat),
  n = m -> S n = S m.
Proof.
    intros n m H.
    f_equal.
    apply H.
Qed.


Check (3 = 3).

Check (forall (n m : nat), n + m = m + n).

(* First-class Citizen *)

Definition is_three (n : nat) : Prop :=
    n = 3.

Definition injective {A B} (f : A -> B) : Prop :=
    forall (x y : A), f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  (* unfold injective. *)
  intros x y H.
  injection H as H1.
  apply H1.
Qed.

Check eq.

Check @eq.

Check (2 = 3).


Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
    split.
    - reflexivity.
    - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
    intros A B HA HB.
    split.
    - apply HA.
    - apply HB.
Qed.

Example and_exmaple' : 3 + 4 = 7 /\ 2  * 2 = 4.
Proof.
    apply and_intro.
    - reflexivity.
    - reflexivity.
Qed.

Lemma and_example2 : forall n m,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
    intros n m H.
    destruct H as [Hn Hm].
    rewrite Hn.
    rewrite Hm.
    reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
    intros P Q [HP _].
    apply HP.
Qed.


Lemma factor_is_0 : forall n m,
  (n = 0 \/ m = 0) -> n * m = 0.
Proof.
    intros n m H.
    destruct H as [Hn | Hm].
    - rewrite Hn.
      reflexivity.
    - rewrite Hm.
      rewrite Nat.mul_comm.
      reflexivity.
Qed.

(*
destruct H as [Hn Hm].
destruct H as [Hn | Hm].
*)

(* Propositions as Types *)


Inductive Or : Type :=
  | One (p : Prop)
  | Two (p : Prop).


(*
discriminate

One p = Two p
*)

(*
injection

One p = One q -> p = q

S n = S m -> n = m
*)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
    intros A B HA.
    - left.
      apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
    intros n.
    destruct n.
    - left.
      reflexivity.
    - right.
      reflexivity.
Qed.


(*
forall Q : Prop, P -> Q
*)

Module NotPlayground.

Definition not (P : Prop) : Prop := P -> False.

Notation "~ x" := (not x) : type_scope.

End NotPlayground.


(* Theorem ex_falso_quodlibet : forall P : Prop,
   False -> P.
Proof.
    intros P H.
    destruct H.
Qed. *)


(* Notation "x <> y" := (not (x = y)). *)

Theorem zero_not_one : 0 <> 1.
Proof.
    (*
    0 <> 1
    not (0 = 1)
    (0 = 1) -> False
    *)
    unfold not.
    intros H.
    discriminate H.
Qed.

Theorem not_False : not False.
Proof.
    unfold not.
    intros H.
    destruct H.
Qed.


Theorem contradiction_implies_anything: forall P Q : Prop,
    (P /\ ~ P) -> Q.
Proof.
    intros P Q H.
    (*
    P /\ ~ P
    P /\ not P
    P /\ (P -> False)
    *)
    destruct H as [HP HnotP].
    unfold not in HnotP.
    apply HnotP in HP.
    destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
    intros P H.
    unfold not.
    intros H2.
    apply H2 in H.
    destruct H.
    (*
    apply H2.
    apply H.
    *)
Qed.


Theorem ex_falso_quodlibet : forall P : Prop,
   False -> P.
Proof.
    intros P H.
    destruct H.
Qed.


Theorem not_true_is_false: forall b : bool,
  b <> true -> b = false.
Proof.
    intros b H.
    destruct b.
    - unfold not in H.
      exfalso.
      apply H.
      reflexivity.
    - reflexivity.
Qed.
