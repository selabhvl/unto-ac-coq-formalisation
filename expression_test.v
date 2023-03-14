Require Import expression.
Require Import String.
Definition n:string := "n".

Lemma val_test: <{val n = (5*5) ; n * 2}> -->* 50.
Proof.
apply multi_step with (y := <{val n = 25 ; n * 2}>).
apply ST_Let1. apply ST_prod. reflexivity.
apply multi_step with (y := <{25*2}>).
apply ST_LetValue. apply v_nat.
apply multi_single. apply ST_prod. reflexivity.
Qed.


Lemma bigstep_val: <{val n = (5*5) ; n * 2}> ==> 50.
Proof.
apply ST_Val with (w1:=25). 
-apply ST_Prod. reflexivity.
-simpl. apply ST_Prod. reflexivity.
Qed.

Definition prod5: string := "prod5".
Lemma bigstep_fun: <{fun prod5 [x:Nat] {x * 5} 5}> ==> 25.
Proof.
apply ST_Fun. simpl.
- apply v_nat.
- apply ST_Prod. reflexivity.
Qed.





