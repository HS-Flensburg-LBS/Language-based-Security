
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.


Open Scope string_scope.


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


Definition fact : Instr :=
  mov r2 (nvalue 1);
  jump (lvalue "factloop").

Definition factloop : Instr :=
  cjump r1 (lvalue "done");
  mov r4 (lvalue "factcont");
  jump (lvalue "prod").

Definition factcont : Instr :=
  (* r3 = r1 * r2  *)
  add r1 r1 (nvalue (-1));
  jump (lvalue "factloop").

Definition use : Instr :=
  mov r1 (nvalue 3);
  jump (lvalue "fact").


(*
int fact(int n) {
  int r = 1;
  while (n != 0) {
    r = r * n;
    n = n - 1;
  }
  return r;
}
*)


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
      eval (H, R, mov rd v ; I) (H, updateRegs R rd (hat R v), I)
| ADD :
    forall (H : Heap) (R : Regs) (I : Instr) (rd rs : reg) (v : value) (n1 n2 : Z), 
      R rs = nvalue n1
      -> hat R v = nvalue n2
      -> eval (H, R, add rd rs v ; I) (H, updateRegs R rd (nvalue (n1 + n2)), I)
| IF_EQ :
    forall (H : Heap) (R : Regs) (I I' : Instr) (r : reg) (v : value) (s : string),
      R r = nvalue 0
      -> hat R v = lvalue s
      -> H s = Some I'
      -> eval (H, R, cjump r v ; I) (H, R, I')
| IF_NEQ :
    forall (H : Heap) (R : Regs) (I : Instr) (r : reg) (v : value) (n : Z),
      R r = nvalue n
      -> n <> 0%Z
      -> eval (H, R, cjump r v ; I) (H, R, I).


Notation "s1 --> s2" := (eval s1 s2) (at level 50).


Definition relation (X : Type) := X -> X -> Prop.


Inductive clos_refl_trans (X : Type) (r : relation X) : relation X :=
| rt_step :
    forall (x y : X),
      r x y -> clos_refl_trans X r x y
| rt_refl :
    forall (x : X),
      clos_refl_trans X r x x
| rt_trans :
    forall (x y z : X),
      clos_refl_trans X r x y -> clos_refl_trans X r y z -> clos_refl_trans X r x z.


Notation "s1 -->* s2" := (clos_refl_trans MState eval s1 s2) (at level 50).


Definition H (str : string) : option Instr :=
  match str with
  | "prod" => Some prod'
  | "loop" => Some loop'
  | "done" => Some done'
  | _      => None
  end.


Compute (H "loop").


Definition R0 (r : reg) : value :=
  match r with
  | r1 => nvalue 2
  | r2 => nvalue 2
  | r3 => nvalue 0
  | r4 => nvalue 0
  end.


Require Import FunctionalExtensionality.


Example eval_prod_loop :
  (H, R0, jump (lvalue "prod")) -->* (H, R0, jump (lvalue "loop")).
Proof.
  eapply rt_trans.
  - apply rt_step.
    apply JUMP with (s := "prod").
    + reflexivity.
    + reflexivity.
  - eapply rt_trans.
    + apply rt_step.
      unfold prod'.
      apply MOV.
    + simpl.
      assert (H: updateRegs R0 r3 (nvalue 0) = R0).
      * extensionality r'.
        destruct r'; reflexivity.
      * rewrite H.
        apply rt_refl.
Qed.

(*
We can extract the proposition we have asserting in the proof above as a 
separate lemma 
 *)
Lemma update_regs_same :
  forall R r,
    updateRegs R r (R r) = R.
Proof.
  intros R r.
  extensionality r'.
  destruct r'; destruct r; reflexivity.
Qed.

Example eval_prod_loop_lemma :
  (H, R0, jump (lvalue "prod")) -->* (H, R0, jump (lvalue "loop")).
Proof.
  eapply rt_trans.
  - apply rt_step.
    apply JUMP with (s := "prod").
    + reflexivity.
    + reflexivity.
  - eapply rt_trans.
    + apply rt_step.
      unfold prod'.
      apply MOV.
    + simpl.
      rewrite update_regs_same.
      apply rt_refl.
Qed.

Example eval_prod_loop_automation :
  (H, R0, jump (lvalue "prod")) -->* (H, R0, jump (lvalue "loop")).
Proof.
  eapply rt_trans.
  - apply rt_step.
    econstructor; reflexivity.
  - eapply rt_trans.
    + apply rt_step.
      apply MOV.
    + rewrite update_regs_same.
      apply rt_refl.
Qed.


Close Scope string_scope.