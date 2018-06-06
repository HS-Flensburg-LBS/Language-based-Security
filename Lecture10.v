
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Lecture09.


Definition R1 (r : reg) : value :=
  match r with
  | r1 => nvalue 1
  | r2 => nvalue 2
  | r3 => nvalue 2
  | r4 => nvalue 0
  end.


Require Import FunctionalExtensionality.


Example eval_loop_loop :
  (H, R0, jump (lvalue "loop")) -->* (H, R1, jump (lvalue "loop")).
Proof.
  eapply rt_trans.
  - apply rt_step.
    Print eval.
    eapply JUMP.
    + reflexivity.
    + reflexivity.
  - eapply rt_trans.
    + apply rt_step.
      unfold loop'.
      eapply IF_NEQ.
      * reflexivity.
      * unfold not.
        intros H.
        inversion H.
    + eapply rt_trans.
      * apply rt_step.
        apply ADD.
        -- reflexivity.
        -- reflexivity.
      * simpl.
        eapply rt_trans.
        -- apply rt_step.
           apply ADD.
           ++ reflexivity.
           ++ reflexivity.
        -- simpl.
           assert (H: updateRegs (updateRegs R0 r3 (nvalue 2)) r1 (nvalue 1) = R1).
           ++ extensionality r'.
              destruct r'; reflexivity.
           ++ rewrite H.
              apply rt_refl.
Qed.
              
(* 
extensionality:

forall x. f x = g x -> f = g
*)

Example eval_prod :
  exists (R : Regs),
    (H, R0, jump (lvalue "prod")) -->* (H, R, jump (rvalue r4)) /\ R r3 = nvalue 4.
Proof.
Admitted.


(* Types *)

Inductive TAL0Type : Type :=
| int : TAL0Type
| code : (reg -> TAL0Type) -> TAL0Type.


Definition RegTypes := reg -> TAL0Type.

Definition LabelTypes := string -> option TAL0Type.


(* Definition updateRegs (R : Regs) (r : reg) (v : value) : Regs := *)
Definition updateRegs (R : reg -> value) (r : reg) (v : value) : reg -> value :=
  fun r' => if beq_reg r r' then v else R r'.

(* Definition updateRegTypes (Gamma : RegTypes) (r : reg) (tau : TAL0Type) : RegTypes := *)
Definition updateRegTypes (Gamma : reg -> TAL0Type) (r : reg) (tau : TAL0Type) : reg -> TAL0Type :=
  fun r' => if beq_reg r r' then tau else Gamma r'.


Definition update (A : Type) (R : reg -> A) (r : reg) (v : A) : reg -> A :=
  fun r' => if beq_reg r r' then v else R r'.


Lemma update_same :
  forall (A : Type) (R : reg -> A) (r : reg),
    update A R r (R r) = R.
Proof.
  intros A R r.
  extensionality r'.
  destruct r'; destruct r; reflexivity.
Qed.


Inductive value_has_type : LabelTypes -> value -> TAL0Type -> Prop :=
| S_INT :
    forall (Psi : LabelTypes) (n : Z),
      value_has_type Psi (nvalue n) int
| S_LAB :
    forall (Psi : LabelTypes) (l : string) (t : TAL0Type),
      Psi l = Some t -> value_has_type Psi (lvalue l) t.

Inductive operand_has_type : LabelTypes -> RegTypes -> value -> TAL0Type -> Prop :=
| S_REG :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (r : reg),
      operand_has_type Psi Gamma (rvalue r) (Gamma r)
| S_VAL :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (tau : TAL0Type),
       value_has_type Psi v tau -> operand_has_type Psi Gamma v tau.

Inductive instr_has_type : LabelTypes -> instr -> RegTypes -> RegTypes -> Prop :=
| S_MOV :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (tau : TAL0Type) (rd : reg),
      operand_has_type Psi Gamma v tau
      -> instr_has_type Psi (mov rd v) Gamma (update TAL0Type Gamma rd tau)
| S_ADD :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (rs : reg) (rd : reg),
      operand_has_type Psi Gamma (rvalue rs) int
      -> operand_has_type Psi Gamma v int
      -> instr_has_type Psi (add rd rs v) Gamma (update TAL0Type Gamma rd int)
| S_IF :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (rs : reg) (v : value),
      operand_has_type Psi Gamma (rvalue rs) int 
      -> operand_has_type Psi Gamma v (code Gamma)
      -> instr_has_type Psi (cjump rs v) Gamma Gamma.
