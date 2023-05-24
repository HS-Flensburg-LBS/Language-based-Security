Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.Pnat.


Lemma True_is_true : True.
Proof.
    apply I.
Qed.

Definition disc_fn (n : nat) : Prop :=
    match n with
    | O => True
    | S _ => False
    end.

Theorem disc_example : forall n, ~(O = S n).
Proof.
    unfold not.
    intros n H.
    assert (H2 : disc_fn O).
    - simpl.
      apply I.
    - rewrite H in H2.
      simpl in H2.
      destruct H2.
Qed.

Lemma add_comm3 :
    forall x y z : nat, x + (y + z) = (z + y) + x.
Proof.
    intros x y z.

Check Nat.add_comm.
Check (Nat.add_comm y).

    rewrite (Nat.add_comm y).
    rewrite Nat.add_comm with (n := x).
    reflexivity.
Qed.


Definition eqb (n1 n2 : nat) : bool :=
    match n1 with
    | O => true
    | S _ => false
    end.


Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition Even x := exists n : nat, x = double n.


Lemma even_42_bool : even 42 = true.
Proof.
   reflexivity.
Qed.

Lemma even_42_prop : Even 42.
Proof.
    unfold Even.
    exists 21.
    reflexivity.
Qed.

Lemma even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
Admitted.