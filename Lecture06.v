
(* Varying the Induction Hypothesis *)

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

Theorem double_injective :
  forall n m : nat,
    double n = double m -> n = m.
Proof.
  intros n m H.
  induction n as [| n' IHn'].
  - simpl in H.
    destruct m as [| m'].
    + reflexivity.
    + simpl in H.
      inversion H.
  - simpl in H.
Abort.

Theorem double_injective' :
  forall n m : nat,
    double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m H.
    simpl in H.
    destruct m as [| m'].
    + reflexivity.
    + simpl in H.
      inversion H.
  - intros m H.
    simpl in H.
    destruct m as [| m'].
    + simpl in H.
      inversion H.
    + simpl in H.
      inversion H.
      clear H.
      apply IHn' in H1.
      rewrite H1.
      reflexivity.
Qed.

Theorem double_injective'' :
  forall n m : nat,
    double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n' IHn']; intros m H; destruct m as [| m'];
    try reflexivity; inversion H; subst; clear H.
  - apply IHn' in H1.
    rewrite H1.
    reflexivity.
Qed.


Theorem double_injective''' :
  forall n m : nat,
    double n = double m -> n = m.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [| m' IHm'].
  - intros n H.
    simpl in H.
    destruct n as [| n'].
    + reflexivity.
    + simpl in H.
      inversion H.
  - intros n H.
    simpl in H.
    destruct n as [| n'].
    + simpl in H.
      inversion H.
    + simpl in H.
      inversion H.
      clear H.
      apply IHm' in H1.
      rewrite H1.
      reflexivity.
Qed.


(* Typed Arithmetic Expressions *)

Require Import Lecture02.
Require Import Lecture05.


Inductive ttype : Type :=
| tBool : ttype.

Inductive hasType : term -> ttype -> Prop :=
| T_True : hasType ttrue tBool
| T_False : hasType tfalse tBool
| T_If :
    forall (t1 t2 t3 : term) (T : ttype),
      hasType t1 tBool -> hasType t2 T -> hasType t3 T -> hasType (tif t1 t2 t3) T.

Example test_hasType :
  hasType (tif ttrue ttrue (tif tfalse tfalse tfalse)) tBool.
Proof.
  apply T_If.
  - apply T_True.
  - apply T_True.
  - apply T_If.
    + apply T_False.
    + apply T_False.
    + apply T_False.
Qed.


Lemma canonical_forms_bool :
  forall v : term,
    value v -> hasType v tBool -> v = ttrue \/ v = tfalse.
Proof.
  intros v Hvalue Htype.
  inversion Hvalue; subst; clear Hvalue.
  - left.
    reflexivity.
  - right.
    reflexivity.
  - inversion H; subst; clear H.
    + inversion Htype.
    + inversion Htype.
Qed. 


Theorem progress :
  forall (t : term) (T : ttype),
    hasType t T -> value t \/ exists (t' : term), t --> t'.
Proof.
  intros t T Htype.
  induction Htype.
  - left.
    apply v_ttrue.
  - left.
    apply v_tfalse.
  - right.
    destruct IHHtype1 as [Hvalue | Hexists].
    + apply canonical_forms_bool in Hvalue.
      * destruct Hvalue as [Htrue | Hfalse]; subst.
        -- exists t2.
           apply E_IfTrue.
        -- exists t3.
           apply E_IfFalse.
      * apply Htype1.
    + destruct Hexists as [t' Heval].
      exists (tif t' t2 t3).
      apply E_If.
      apply Heval.
Qed.


Theorem preservation :
  forall (t t' : term) (T : ttype),
    hasType t T -> t --> t' -> hasType t' T.
Proof.
  intros t t' T HhasType.
  generalize dependent t'.
  induction HhasType.
  - intros t' Heval.
    inversion Heval.
  - intros t' Heval.
    inversion Heval.
  - intros t' Heval.
    inversion Heval; subst; clear Heval.
    + apply HhasType2.
    + apply HhasType3.
    + apply T_If.
      * apply IHHhasType1.
        apply H3.
      * apply HhasType2.
      * apply HhasType3.
Qed.        
