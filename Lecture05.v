
Require Import Lecture02.

Inductive numeric_value : term -> Prop :=
| nv_tzero : numeric_value tzero
| nv_tsucc :
    forall (nv : term),
      numeric_value nv -> numeric_value (tsucc nv).

Inductive value : term -> Prop :=
| v_ttrue : value ttrue
| v_tfalse : value tfalse
| v_nv :
    forall (nv : term),
      numeric_value nv -> value nv.

Inductive eval : term -> term -> Prop :=
| E_IfTrue :
    forall (t2 t3 : term),
      eval (tif ttrue t2 t3) t2
| E_IfFalse :
    forall (t2 t3 : term),
      eval (tif tfalse t2 t3) t3
| E_If :
    forall (t1 t1' t2 t3 : term),
      eval t1 t1' -> eval (tif t1 t2 t3) (tif t1' t2 t3)
| E_Succ :
    forall (t1 t1' : term),
      eval t1 t1' -> eval (tsucc t1) (tsucc t1')
| E_PredZero :
    eval (tpred tzero) tzero
| E_PredSucc :
    forall (nv1 : term),
      numeric_value nv1 -> eval (tpred (tsucc nv1)) nv1
| E_Pred :
    forall (t1 t1' : term),
      eval t1 t1' -> eval (tpred t1) (tpred t1')
| E_IszeroZero :
    eval (tiszero tzero) ttrue
| E_IszeroSucc :
    forall (t : term),
      numeric_value t -> eval (tiszero (tsucc t)) tfalse
| E_Iszero :
    forall (t1 t1' : term),
      eval t1 t1' -> eval (tiszero t1) (tiszero t1').

Notation "t1 --> t2" := (eval t1 t2) (at level 50) : type_scope.


(* 
We cannot perform the following evaluation because the argument
of tsucc has to be a numeric value.
 *)

Example test_eval_stuck :
  not (tpred (tsucc tfalse) --> tfalse).
Proof.
  unfold not.
  intros H.
  inversion H.
  inversion H1.
Qed.

(*
We cannot perform the following evaluation because we have to perform
more than a single step.
*)

Example test_multi_step :
  not (tpred (tsucc (tpred tzero)) --> tzero).
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.


(* Relation *)

Definition relation (X : Type) :=
  X -> X -> Prop.

Check (relation nat).

Check le.


Inductive next_nat : relation nat :=
| nn : forall n : nat, next_nat n (S n).


Example test_next_nat :
  next_nat 4 5.
Proof.
  apply nn.
Qed.

Example test_next_nat2 :
  not (next_nat 3 5).
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.


Definition reflexive (X : Type) (R : relation X) :=
(* Definition reflexive (X : Type) (R : X -> X -> Prop) :=   *)
  forall x : X, R x x.

Theorem le_refl :
  reflexive nat le.
Proof.
  unfold reflexive.
  intros x.
  Check le.
  Print le.
  apply le_n.
Qed.  

Example test_le :
  not (le 10 2).
Proof.
  unfold not.
  intros H.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H0.
Qed.

Definition transitive (X : Type) (R : relation X) : Prop :=
  forall a b c : X, R a b -> R b c -> R a c.


(* a <= b /\ b <= c -> a <= c *)

(* le a b /\ le b c -> le a c *)

(* R a b /\ R b c -> R a c *)

(* R a b -> R b c -> R a c *)


Theorem le_trans :
  transitive nat le.
Proof.
  unfold transitive.
  intros a b c Hab Hbc.
  induction Hbc; subst.
  - apply Hab.
  - apply le_S.
    apply IHHbc.
Qed.    


Theorem lt_trans :
  transitive nat lt.
Proof.
  unfold transitive.
  intros x y z Hxy Hyz.
  unfold lt.
  unfold lt in Hxy.
  unfold lt in Hyz.
  apply le_trans with (a := S x) (b := S y) (c := z).
  - apply le_S.
    apply Hxy.
  - apply Hyz.
Qed.


(* Definition reltion X = X -> X -> Prop. *)


Inductive clos_refl_trans (X : Type) (R : relation X) : relation X :=
(* Inductive clos_refl_trans (X : Type) (R : relation X) : X -> X -> Prop := *)
| rt_step :
    forall x y : X,
      R x y -> clos_refl_trans X R x y
| rt_refl :
    forall x : X,
      clos_refl_trans X R x x
| rt_trans :
    forall x y z : X,
      clos_refl_trans X R x y -> clos_refl_trans X R y z -> clos_refl_trans X R x z.

Notation "t -->* t'" := (clos_refl_trans term eval t t') (at level 50).


(* Unset Printing Notations. *)


Example test_mult_eval1 :
  tfalse -->* tfalse.
Proof.
  (* Does not work because we do not perform a step *)
  (* apply rt_step. *)
  apply rt_refl.
Qed.

Example test_mult_eval2 :
  tif ttrue ttrue (tif tfalse tfalse tfalse) -->* ttrue.
Proof.
  apply rt_step.
  apply E_IfTrue.
Qed.

Example test_multi_eval3 :
  tpred (tsucc (tpred tzero)) -->* tzero.
Proof.
  apply rt_trans with (y := tpred (tsucc tzero)).
  - apply rt_step.
    apply E_Pred.
    apply E_Succ.
    apply E_PredZero.
  - apply rt_step.
    apply E_PredSucc.
    apply nv_tzero.
Qed.


(* Semantic Styles

# Operational Semantics
## Small-Step Semantics
## Big-Step Semantics

# Denotational Semantics

 *)
