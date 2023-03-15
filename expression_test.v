


Require Import expression.
Require Import String.
Require Import Lia.


(*NOTATION*)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition n : string := "n".
Definition fun0: string := "prod5". 
Definition prod5: string := "prod5". 

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Check <{x}>.
Check <{fun prod5 [x:Nat] {x * 5} 5}>.
Check <{x (fun prod5 [x:Nat] {x * 5})}>.
Check <{val n = 25 ; n * 2}>.
Check <{[4 >> 2][5 >> 5][6 >> 4][ > 5]}>.



(*SMALL STEP SEMANTICS*)

Lemma smallstep_pred_succ:forall (n:nat),<{pred (succ n)}> -->* <{n}>.
Proof.
intro n. eapply multi_step. apply ST_pred_step. apply ST_succ. auto.
eapply multi_step. apply ST_pred. simpl. auto. apply multi_refl.
Qed.

(*Test of succ-pred*)
Lemma smallstep_val:forall (n:nat),<{pred (succ n)}> -->* <{n}>.
Proof.
intros n0. induction n0 as [| n' Hd].
- apply multi_step with (y := <{pred 1}>).
  +apply ST_pred_step. apply ST_succ. reflexivity.
  +apply multi_single. apply ST_pred. reflexivity.
- rewrite Hd.

(*Test of val*)
Lemma smallstep_val: <{val n = (5*5) ; n * 2}> -->* 50.
Proof.
apply multi_step with (y := <{val n = 25 ; n * 2}>).
apply ST_Let1. apply ST_prod. reflexivity.
apply multi_step with (y := <{25*2}>).
apply ST_LetValue. apply v_nat.
apply multi_single. apply ST_prod. reflexivity.
Qed.

(*Test of fun*)
Lemma smallstep_fun: <{fun prod5 [x:Nat] {x * 5} 5}> -->* 25.
Proof.
apply multi_step with (y := <{5 * 5}>).
- apply ST_AppAbs. apply v_nat.
- apply multi_single. apply ST_prod. reflexivity.
Qed.


(*BIG STEP SEMANTICS*)

Lemma smallstep_pred_succ:forall (n:nat),<{pred (succ n)}> -->* <{n}>.
Proof.
intro n. eapply multi_step. apply ST_pred_step. apply ST_succ. auto.
eapply multi_step. apply ST_pred. simpl. auto. apply multi_refl.
Qed.


(*Test of val*)
Lemma bigstep_val: <{val n = (5*5) ; n * 2}> ==> 50.
Proof.
apply ST_Val with (w1:=25). 
-apply ST_Prod. reflexivity.
-simpl. apply ST_Prod. reflexivity.
Qed.

Lemma bigstep_fun: <{fun prod5 [x:Nat] {x * 5} 5}> ==> 25.
Proof.
apply ST_Fun. simpl.
- apply v_nat.
- apply ST_Prod. reflexivity.
Qed.





