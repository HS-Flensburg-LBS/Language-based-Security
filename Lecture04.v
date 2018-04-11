
Require Import Lecture01.

(* Homework *)

Theorem curry :
  forall p q r : Prop,
    (p /\ q -> r) <-> (p -> q -> r).
Proof.
  intros p q r.
  split.
  - intros H Hp Hq.
    apply H.
    split.
    + apply Hp.
    + apply Hq.
  - intros H [Hp Hq].
    apply H.
    + apply Hp.
    + apply Hq.
Qed.


(* Inductively Defined Propositions *)

(* ev_O : O is even *)
(* ev_SS : if n even, then S (S n) is even *)

Inductive even : nat -> Prop :=
| ev_O : even O
| ev_SS : forall n : nat,
    even n -> even (S (S n)).

Theorem ev_4 : even 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_O.
Qed.

Theorem ev_plus4 :
  forall m : nat, even m -> even (4 + m).
Proof.
  intros m H.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Theorem ev_minus2 :
  forall m : nat, even m -> even (pred (pred m)).
Proof.
  intros m H.
  inversion H as [H' | n' H'].
  - simpl.
    apply ev_O.
  - simpl.
    apply H'.
Qed.

Inductive term : Type :=
| ttrue : term
| tfalse : term
| tzero : term
| tsucc : term -> term
| tpred : term -> term
| tiszero : term -> term
| tif : term -> term -> term -> term.

Inductive value : term -> Prop :=
| v_ttrue : value ttrue
| v_tfalse : value tfalse.

Example true_value : value ttrue.
Proof.
  apply v_ttrue.
Qed.

(* Negation *)

Module MyNot.

  Definition not (P : Prop) := P -> False.

  Check not.

  Check iff.

End MyNot.

Theorem ex_false_quodlibet :
  forall (P : Prop),
    False -> P.
Proof.
  intros P H.
  destruct H.
Qed.

Theorem zero_not_one :
  (* not (0 = 1). *)
  0 <> 1.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Theorem double_neg :
  forall (P : Prop),
    P -> not (not P).
Proof.
  intros P H.
  (* unfold unfolds not twice *)
  unfold not.
  (* not (not P) becomes not P -> False  (P -> False) -> False *)
  intros HP.
  apply HP in H.
  inversion H.
Qed.

Theorem one_not_even :
  not (even 1).
Proof.
  unfold not.
  intros Hev1.
  inversion Hev1.
Qed.

Theorem tif_not_value :
  not (value (tif tfalse ttrue tfalse)).
Proof.
  unfold not.
  intros Hvalue.
  inversion Hvalue.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Example test_double :
  double 13 = 26.
Proof.
  reflexivity.
Qed.

(* Induction over inductive propositions *)

Lemma ev_even :
  forall n : nat,
    even n -> exists k : nat, n = double k.
Proof.
  intros n Heven.
  induction Heven as [| n' Heven' IHn'].
  - exists 0.
    reflexivity.
  - destruct IHn' as [k' Hk'].
    exists (S k').
    rewrite Hk'.
    reflexivity.
Qed.    

(* Inductive Relation *)

Inductive le : nat -> nat -> Prop :=
| le_n : forall n : nat, le n n
| le_S : forall n m : nat, le n m -> le n (S m).

Notation "m <= n" := (le m n).

Theorem test_le1 : le 3 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2 : 3 <= 6.
Proof.
  do 3 apply le_S.
  apply le_n.
Qed.

Theorem test_le3 : 2 <= 1 -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.

Definition lt (n m : nat) : Prop :=
  le (S n) m.

Inductive eval : term -> term -> Prop :=
| E_IfTrue : forall t2 t3 : term,
    eval (tif ttrue t2 t3) t2
| E_IfFalse : forall t2 t3 : term,
    eval (tif tfalse t2 t3) t3
| E_If : forall t1 t1' t2 t3 : term,
    eval t1 t1' -> eval (tif t1 t2 t3) (tif t1' t2 t3).


Notation "t1 --> t2" := (eval t1 t2) (at level 50, left associativity) : type_scope.


Example test_eval1 :
  tif ttrue ttrue (tif tfalse tfalse tfalse) --> ttrue.
Proof.
  apply E_IfTrue.
Qed.

Example test_eval2 :
  tif tfalse ttrue (tif tfalse tfalse tfalse) --> tif tfalse tfalse tfalse.
Proof.
  apply E_IfFalse.
Qed.

Example test_eval3 :
  tif (tif ttrue ttrue tfalse) ttrue (tif tfalse tfalse tfalse)
      -->
      tif ttrue ttrue (tif tfalse tfalse tfalse).
Proof.
  apply E_If.
  apply E_IfTrue.
Qed.
