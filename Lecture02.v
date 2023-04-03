
(* Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
    intros n.
    (* plus O n = n *)
    simpl.
    reflexivity.
Qed.

(*
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y). *)

(* 1 = S O *)

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
    intros n.
    (*
    plus (S O) n
    -> S (plus O n)
    -> S n
    *)
    simpl.
    reflexivity.
Qed.

Theorem mult_0_l: forall n : nat, 0 * n = 0.
Proof.
    intros n.
    (*
    mult O n
    -> O
    *)
    simpl.
    reflexivity.
Qed.

(*
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O ⇒ O
  | S n' ⇒ plus m (mult n' m)
  end.
*)

(* Proof by Rewriting *)

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite <- H.
    reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0: forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity.
Qed.

(* Proof by Case Analysis *)

Theorem plus_1_neq_0: forall n : nat,
    Nat.eqb (n + 1) 0 = false.
Proof.
    intros [| n'].
    (* destruct n as [| n'] eqn:E. *)
    - reflexivity.
    - reflexivity.
Qed.

(*
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ eqb n' m'
            end
  end.
  *)

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b.
    destruct b eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

(*
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
*)

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
Qed.

Theorem andb_commutative' : forall b c,
  andb b c = andb c b.
Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

(*
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
*)

(* Unfolding *)
