
Require Import Lecture01.


(* The apply Tactic *)

Theorem silly1 :
  forall n m o p : nat,
    n = m -> (n,o) = (n,p) -> (n,o) = (m,p).
Proof.
  intros n m o p Hn Hm.
  rewrite <- Hn.
  apply Hm.
Qed.

Theorem silly2 :
  forall n m o p : nat,
    n = m -> (forall q r : nat, q = r -> (q,o) = (r,p)) -> (n,o) = (m,p).
Proof.
  intros n m o p Heq Hqr.
  apply Hqr.
  apply Heq.
Qed.

Theorem silly3_firsttry :
  forall n : nat,
    true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  symmetry.
  apply H.
Qed.

(* The apply ... with ... Tactic *)

Theorem trans_eq_example :
  forall a b c d e f : nat,
    (a,b) = (c,d) -> (c,d) = (e,f) -> (a,b) = (e,f).
Proof.
  intros a b c d e f Heq1 Heq2.
  rewrite Heq1.
  apply Heq2.
Qed.

(*
The previous proposition holds more general. The concept of generics as known
from Java, for example, can be used to generalize statements to arbitrary types.
In PLT (programming language theory) the concept of generics is called
parametric polymorphism.
*)

Theorem trans_eq :
  forall (X : Type) (x y z : X),
    x = y -> y = z -> x = z.
Proof.
  intros X x y z Heq1 Heq2.
  rewrite Heq1.
  apply Heq2.
Qed.

Theorem trans_eq_example' :
  forall a b c d e f : nat,
    (a,b) = (c,d) -> (c,d) = (e,f) -> (a,b) = (e,f).
Proof.
  intros a b c d e f Heq1 Heq2.
  apply trans_eq with (y := (c,d)).
  - apply Heq1.
  - apply Heq2.
Qed.


(* Term data type from second lecture *)

Inductive term : Type :=
| ttrue : term
| tfalse : term
| tzero : term
| tsucc : term -> term
| tpred : term -> term
| tiszero : term -> term
| tif : term -> term -> term -> term.

Fixpoint size (t : term) : nat :=
  match t with
  | ttrue => 1
  | tfalse => 1
  | tzero => 1
  | tsucc t' => size t' + 1
  | tpred t' => size t' + 1
  | tiszero t' => size t' + 1
  | tif t1 t2 t3 => size t1 + size t2 + size t3 + 1
  end.

(* Imports lists *)
Require Import Coq.Lists.List.
(* Imports notation for lists, for example [x] for a singleton list *)
Import ListNotations.

Fixpoint consts (t : term) : list term :=
  match t with
  | ttrue => [ttrue]
  | tfalse => [tfalse]
  | tzero => [tzero]
  | tsucc t' => consts t'
  | tpred t' => consts t'
  | tiszero t' => consts t'
  | tif t1 t2 t3 => consts t1 ++ consts t2 ++ consts t3
  end.

(*
Induction on natural numbers can be generalized to arbitrary inductive data
types. An induction over a term of an inductive data type is called structural
induction.
*)

(* The following lemma will be helpful in the proof of the subsequent theorem *)

Lemma le_plus_1 :
  forall n m : nat, n <= m -> n <= m + 1.
Proof.
  intros n m H.
  rewrite PeanoNat.Nat.add_comm.
  apply le_S.
  apply H.
Qed.

Theorem consts_size :
  forall t : term, length (consts t) <= size t.
Proof.
  induction t as [ | | | t' IHt' | t' IHt' | t' IHt' | t1 IHt1 t2 IHt2 t3 IHt3 ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl consts.
    simpl size.
    rewrite PeanoNat.Nat.add_comm.
    simpl "+".
    apply le_S.
    apply IHt'.
    (*
    The proof of this subgoal contains some steps for illustration purposes.
    With the lemma le_plus_1 at hand we can simplify the cases for unary
    constructors.
     *)
  - apply le_plus_1.
    apply IHt'.
  - apply le_plus_1.
    apply IHt'.
  - simpl.
    apply le_plus_1.
    (*
    The command Search searches for propositions. We can provide a pattern to
    search for propositions of a specific form.
     *)
    Search (length (_ ++ _) = _).
    Check app_length.
    rewrite app_length.
    rewrite app_length.
    (*
    The additions on the left and right hand side of the equation are structured
    differently, therefore, we have to changes the parens.
     *)
    Search (_ + (_ + _) = (_ + _) + _).
    Check PeanoNat.Nat.add_assoc.
    rewrite PeanoNat.Nat.add_assoc.
    (*
    Now we need a property of less equal.
     *)
    Search (_ <= _ -> _ <= _ -> _ + _ <= _ + _).
    Check Plus.plus_le_compat.
    apply Plus.plus_le_compat.
    + apply Plus.plus_le_compat.
      * apply IHt1.
      * apply IHt2.
    + apply IHt3.
Qed.

(*
Repetition of basic terminology:
 - left associative, right associative
 - commutativity
 - associativity
 - reflexivity
 - symmetry
 - transitivity
 *)

(* We do the proof again in a minimal form *)
Theorem consts_size' :
  forall t : term, length (consts t) <= size t.
Proof.
  induction t as [ | | | t' IHt' | t' IHt' | t' IHt' | t1 IHt1 t2 IHt2 t3 IHt3 ].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply le_plus_1.
    apply IHt'.
  - apply le_plus_1.
    apply IHt'.
  - apply le_plus_1.
    apply IHt'.
  - simpl.
    apply le_plus_1.
    rewrite app_length.
    rewrite app_length.
    rewrite PeanoNat.Nat.add_assoc.
    apply Plus.plus_le_compat.
    + apply Plus.plus_le_compat.
      * apply IHt1.
      * apply IHt2.
    + apply IHt3.
Qed.


(* Conjunction *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Theorem and_example2 :
  forall n m : nat,
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* intros n m H. *)
  (* destruct H as [Hn Hm]. *)
  intros n m [Hn Hm].
  rewrite Hn, Hm.
  reflexivity.
Qed.


(* Equivalence *)

Module MyIff.

  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Check (1 = 2).

  Check (iff (1 = 2) (2 = 3)).

  Notation "P <-> Q" := (iff P Q).

End MyIff.

Theorem iff_sym :
  forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.
