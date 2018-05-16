
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.


Inductive reg : Type :=
| r1 : reg
| r2 : reg
| r3 : reg
| r4 : reg.

Definition beq_reg (r r' : reg) : bool :=
  match (r,r') with
  | (r1,r1) => true
  | (r2,r2) => true
  | (r3,r3) => true
  | (r4,r4) => true
  | _ => false
  end.


Inductive value : Type :=
| nvalue : Z -> value
| lvalue : string -> value
| rvalue : reg -> value.

Inductive instr : Type :=
| mov : reg -> value -> instr
| add : reg -> reg -> value -> instr
| cjump : reg -> value -> instr.

Inductive Instr : Type :=
| jump : value -> Instr
| seq : instr -> Instr -> Instr.


Definition prod : Instr :=
  seq (mov r3 (nvalue 0)) (jump (lvalue "loop")).

Definition loop : Instr :=
  seq (cjump r1 (lvalue "done"))
      (seq (add r3 r2 (rvalue r3))
           (seq (add r1 r1 (nvalue (-1)))
                (jump (lvalue "loop")))).

Definition done : Instr :=
  jump (rvalue r4).


Notation "i ; I" := (seq i I) (at level 80, right associativity).

Definition prod' : Instr :=
  mov r3 (nvalue 0);
  jump (lvalue "loop").

Definition loop' : Instr :=
  cjump r1 (lvalue "done");
  add r3 r2 (rvalue r3);
  add r1 r1 (nvalue (-1));
  jump (lvalue "loop").

Definition done' : Instr :=
  jump (rvalue r4).


Definition Regs := reg -> value.

Definition Heap := string -> option Instr.


Definition MState : Type :=
  Heap * Regs * Instr.


Definition hat (R : Regs) (v : value) : value :=
  match v with
  | rvalue r => R r
  | _ => v
  (* | nvalue n => nvalue n *)
  (* | lvalue l => lvalue l *)
  end.

Definition updateRegs (R : Regs) (r : reg) (v : value) : Regs :=
  fun r' => if beq_reg r r' then v else R r'.


Inductive eval : MState -> MState -> Prop :=
| JUMP :
    forall (H : Heap) (R : Regs) (v : value) (I : Instr) (s : string),
      hat R v = lvalue s
      -> H s = Some I
      -> eval (H, R, jump v) (H, R, I)
| MOV :
    forall (H : Heap) (R : Regs) (I : Instr) (rd : reg) (v : value),
      eval (H, R, mov rd v ; I) (H, updateRegs R rd (hat R v), I).
