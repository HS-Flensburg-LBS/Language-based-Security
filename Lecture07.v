
Require Import Lecture02.
Require Import Lecture05.


Lemma swap :
  forall (A B : Prop),
    A \/ B -> B \/ A.
Proof.
  intros A B Hor.
  destruct Hor as [HA | HB].
  - right.
    apply HA.
  - left.
    apply HB.
Qed.    


Inductive option (X : Type) : Type :=
| Some : X -> option X
| None : option X.

(* option nat *)
Check (Some nat 23).
Check (None nat).

(* option bool *)
Check (Some bool true).
Check (None bool).

Arguments Some {X} _.
Arguments None {X}.

Check (Some 23).
Check (Some ttrue).


Fixpoint is_numeric_value (t : term) : bool :=
  match t with
  | tzero => true
  | tsucc t' => is_numeric_value t'
  | _ => false
  end.

Fixpoint evalF (t : term) : option term :=
  match t with
  | ttrue => Some ttrue
  | tfalse => Some tfalse
  | tzero => Some tzero
  | tsucc t1 =>
    match evalF t1 with
    | Some nv => if is_numeric_value nv
                 then Some (tsucc nv)
                 else None                        
    | _ => None
    end
  | tpred t1 => None
  | tiszero t1 => None
  | tif t1 t2 t3 =>
    match evalF t1 with
    | Some tfalse => evalF t3
    | Some ttrue => evalF t2 
    | _ => None
    end
  end.



Compute (evalF (tsucc (tif tfalse tfalse tfalse))).

Compute (evalF (tif ttrue (tsucc tzero) tzero)).


Example test_multi_eval :
  tpred (tsucc (tpred tzero)) -->* tzero.
Proof.
  eapply rt_trans.
  - apply rt_step.
    apply E_Pred.
    repeat constructor.
  - apply rt_step.
    repeat constructor.
Qed.

