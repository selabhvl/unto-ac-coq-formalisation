
Require Import expression.
Require Import small_step_semantics.
Require Import String.

(*NOTATION*)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition n : string := "n".
Definition fun0: string := "fun0". 
Definition prod5: string := "prod5". 

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(*SMALL STEP SEMANTICS*)

Lemma smallstep_pred_succ:forall (n:nat),<{pred (succ n)}> -->* <{n}>.
Proof.
intro n. eapply multi_step. apply ST_pred_step. apply ST_succ. auto.
eapply multi_step. apply ST_pred. simpl. auto. apply multi_refl.
Qed.

(*Test of val*)
Lemma smallstep_val: <{val n = (5*5) ; n * 2}> -->* 50.
Proof.
apply multi_step with (y := <{val n = 25 ; n * 2}>).
apply ST_Let1. apply ST_prod. reflexivity.
eapply multi_step. apply ST_LetValue. apply v_nat.
simpl. apply multi_single. apply ST_prod. reflexivity.
Qed.

Check <{5}>.

(*Test of fun*)
Lemma smallstep_fun: <{fun prod5 [x:Nat] {x * 5} 5}> -->* 25.
Proof.
apply multi_step with (y := <{5*5}>).
- apply ST_AppAbs. apply v_nat.
- apply multi_single. apply ST_prod. reflexivity.
Qed.
