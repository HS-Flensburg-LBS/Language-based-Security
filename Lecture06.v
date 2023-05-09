Require Import Coq.Lists.List.
Import ListNotations.


(*
Prop :=
    Prop /\ Prop
  | Prop \/ Prop
  | ~ Prop
  | Prop <-> Prop
  | Prop -> Prop
  | forall (x : T), Prop
  | exists (x : T), Prop
  | False
  | True
*)

(* Definition not (P : Prop) : Prop :=
    P -> False

Notation ~p := (not p). *)

(*
destruct r as [ n d ]
destruct n as [|]
*)

(*
/\
Hypothese: destruct
Goal: split

\/
Hypothese: destruct
Goal: left / right

~
unfold not

forall (x : T), Prop
Hypothese: apply, rewrite
Goal: intros x

<->
Hypothese:
Goal:
*)

(* exfalso *)

(* H1: x = 3
H2: forall (x : nat), x = 3 *)

(* 4 = 3 *)

(* Lemma helping_lemma : forall x : nat, ... *)


(* Definition x := 1. *)


(*
Definition iff (P Q : Prop) : Prop :=
   (P -> Q) /\ (Q -> P).
*)

(* Notation "P <-> Q" : (iff P Q). *)


Theorem iff_sym: forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
    intros P Q [HPQ HQP].
    split.
    - apply HQP.
    - apply HPQ.
Qed.


Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
    intros b.
    split.
    - intros H.
      apply not_true_is_false.
      apply H.
    - intros H.
      rewrite H.
      intros H'.
      discriminate H'.
Qed.

Lemma apply_iff_example1 :
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
    intros P Q R [HPQ HQP] HQR HP.
    apply HQR.
    apply HPQ.
    apply HP.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Definition Even (m : nat) : Prop :=
    exists (n : nat), m = double n.


Lemma four_is_even : Even 4.
Proof.
    unfold Even.
    exists 2.
    reflexivity.
Qed.

Theorem exists_example_2 : forall n,
   (exists m, n = 4 + m) ->
   (exists o, n = 2 + o).
Proof.
    intros n [m Hm].
    exists (2 + m).
    apply Hm.
Qed.


Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
    match l with
    | [] => False
    | x' :: l' => x' = x \/ In x l'
    end.


Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
    right.
    right.
    right.
    left.
    reflexivity.
Qed.

Example In_example_2 :
  forall n : nat, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
    intros n [ HIn1 | [ HIn2 | [] ] ].
    - exists 1.
      rewrite <- HIn1.
      reflexivity.
    - exists 2.
      rewrite <- HIn2.
      reflexivity.
Qed.


Theorem In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
   In x l -> In (f x) (map f l).
Proof.
    intros A B f l x HIn.
    induction l as [|x' l' IHl'].
    - destruct HIn.
    - destruct HIn.
      + left.
        rewrite H.
        reflexivity.
      + right.
        apply IHl'.
        apply H.
Qed.

