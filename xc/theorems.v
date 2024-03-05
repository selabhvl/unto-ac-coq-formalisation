From AC Require Import syntax.
From AC Require Import big_step_semantics.

From AC Require Import mapping.
Module Theorems (M: MAPPING).

  Module Import BS := BigStepSemantics(M).
  Include BS.


  Definition is_comm_exp (e : exp) : Prop := 
    match e with 
    | exp_app_2 e1 e2 e3 => forall id ss vtIn nval vtOut, 
      <[id | ss | vtIn | e]> ==> <[nval | vtOut]> 
      <->
      <[id | ss | vtIn | (exp_app_2 e1 e3 e2)]> ==> <[nval | vtOut]> 
    | _ => False
    end.

  Fixpoint swap (e commExp : exp) : exp :=
    match e with 
    | exp_var _ => e
    | exp_app_1 e1 e2 => exp_app_1 (swap e1 commExp) (swap e2 commExp)
    | exp_app_2 e1 e2 e3 => exp_app_2 (swap e1 commExp) (swap e2 commExp) (swap e3 commExp) 
    | exp_app_3 e1 e2 e3 e4 => exp_app_3 (swap e1 commExp) (swap e2 commExp) (swap e3 commExp) (swap e4 commExp) 
    | exp_val s e1 e2 => exp_val s (swap e1 commExp) (swap e2 commExp) 
    | exp_literal _ => e
    | exp_nvalue _ => e
    end.

  Theorem use_comm : forall commExp,
    is_comm_exp commExp ->
    forall id ss vtIn nval vtOut exp,
      <[id | ss | vtIn | exp]> ==> <[nval | vtOut]>
      <->
      <[id | ss | vtIn | swap exp commExp]> ==> <[nval | vtOut]>.
  Admitted.

End Theorems.