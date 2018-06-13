
Require Import Lecture09.
Require Import Lecture10.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.


Inductive type : Type :=
| int : type
| code : (reg -> type) -> type
| var : nat -> type
| all : nat -> type -> type.

Definition RegTypes := reg -> type.

Definition LabelTypes := string -> option type.


Inductive value_has_type : LabelTypes -> value -> type -> Prop :=
| S_INT :
    forall (Psi : LabelTypes) (n : Z),
      value_has_type Psi (nvalue n) int
| S_LAB :
    forall (Psi : LabelTypes) (l : string) (tau : type),
      Psi l = Some tau -> value_has_type Psi (lvalue l) tau.

Inductive operand_has_type : LabelTypes -> RegTypes -> value -> type -> Prop :=
| S_REG :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (r : reg),
      operand_has_type Psi Gamma (rvalue r) (Gamma r)
| S_VAL :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (tau : type),
      value_has_type Psi v tau -> operand_has_type Psi Gamma v tau.

Inductive instr_has_type : LabelTypes -> instr -> RegTypes -> RegTypes -> Prop :=
| S_MOV :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (tau : type) (rd : reg),
      operand_has_type Psi Gamma v tau
      -> instr_has_type Psi (mov rd v) Gamma (update type Gamma rd tau)
| S_ADD :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (rs rd : reg),
      operand_has_type Psi Gamma (rvalue rs) int -> operand_has_type Psi Gamma v int
      -> instr_has_type Psi (add rd rs v) Gamma (update type Gamma rd int)
| S_IF :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value) (rs : reg),
      operand_has_type Psi Gamma (rvalue rs) int -> operand_has_type Psi Gamma v (code Gamma)
      -> instr_has_type Psi (cjump rs v) Gamma Gamma.

Inductive Instr_has_type : LabelTypes -> Instr -> type -> Prop :=
| S_JUMP :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (v : value),
      operand_has_type Psi Gamma v (code Gamma)
      -> Instr_has_type Psi (jump v) (code Gamma)
| S_SEQ :
    forall (Psi : LabelTypes) (Gamma Gamma2 : RegTypes) (iota : instr) (I : Instr),
      instr_has_type Psi iota Gamma Gamma2 -> Instr_has_type Psi I (code Gamma2)
      -> Instr_has_type Psi (iota ; I) (code Gamma).

Inductive Regs_has_type : LabelTypes -> Regs -> RegTypes -> Prop :=
| S_REGFILE :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (R : Regs),
      (forall (r : reg), value_has_type Psi (R r) (Gamma r))
      -> Regs_has_type Psi R Gamma.

Inductive Heap_has_type : Heap -> LabelTypes -> Prop :=
| S_HEAP :
    forall (Psi : LabelTypes) (H : Heap),
      (forall (l : string) (I : Instr) (tau : type), H l = Some I -> Psi l = Some tau -> Instr_has_type Psi I tau)
      -> Heap_has_type H Psi.

Inductive State_has_type : MState -> Prop :=
| S_MACH :
    forall (Psi : LabelTypes) (Gamma : RegTypes) (I : Instr) (H : Heap) (R : Regs),
      Heap_has_type H Psi -> Regs_has_type Psi R Gamma -> Instr_has_type Psi I (code Gamma)
      -> State_has_type (H, R, I).


Definition Gamma' (r : reg) : type :=
  match r with
  | r4 => var 7
  | _ => int
  end.

Definition Gamma (r : reg) : type :=
  match r with
  | r4 => all 7 (code Gamma')
  | _ => int
  end.

Open Scope string_scope.

Definition Psi (l : string) : option type :=
  match l with
  | "prod" => Some (code Gamma)
  | "loop" => Some (code Gamma)
  | "done" => Some (code Gamma)
  | _ => None
  end.


Example type_derivation1 :
  instr_has_type Psi (cjump r1 (lvalue "done")) Gamma Gamma.
Proof.
  repeat constructor.
Qed.
(*   apply S_IF. *)
(*   - apply S_REG. *)
(*   - apply S_VAL. *)
(*     apply S_LAB. *)
(*     reflexivity. *)
(* Qed. *)

Example type_derivation2 :
  instr_has_type Psi (add r3 r2 (rvalue r3)) Gamma Gamma.
Proof.
  rewrite <- update_same with (r := r3).
  repeat constructor.
Qed.

Example type_derivation3 : 
  instr_has_type Psi (add r1 r1 (nvalue (-1))) Gamma Gamma.
Proof.
  rewrite <- update_same with (r := r1).
  apply S_ADD.
  - apply S_REG.
  - apply S_VAL.
    apply S_INT.  
Qed.

Example type_derivation4 :
  Instr_has_type Psi (jump (lvalue "loop")) (code Gamma).
Proof.
  apply S_JUMP.
  apply S_VAL.
  apply S_LAB.
  reflexivity.
Qed.

Example type_derivation5 :
  instr_has_type Psi (mov r3 (nvalue 0)) Gamma Gamma.
Proof.
  erewrite <- update_same.
  apply S_MOV.
  apply S_VAL.
  apply S_INT.
Qed.  

Example type_derivation6 :
  Instr_has_type Psi (jump (lvalue "loop")) (code Gamma).
Proof.
  apply S_JUMP.
  apply S_VAL.
  apply S_LAB.
  reflexivity.
Qed.

Example type_derivation_prod :
  Instr_has_type Psi (mov r3 (nvalue 0); jump (lvalue "loop")) (code Gamma).
Proof.
  eapply S_SEQ.
  - apply type_derivation5.
  - apply type_derivation6.
Qed.    

Close Scope string_scope.
