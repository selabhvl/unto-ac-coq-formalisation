From AC Require Import expression.
From AC Require Import big_step_semantics.
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

(*Test of pred succ*)
Lemma bigstep_pred_succ:forall (i:nat), <{pred (succ i)}> ==> <{i}>.
Proof.
intro i.
apply ST_Pred with (n:=(S i)).
-simpl. reflexivity.
-apply ST_Succ with (n:=i). reflexivity. apply ST_Refl.
Qed.

(*Test of val*)
Lemma bigstep_val: <{val n = (5*5) ; n * 2}> ==> 50.
Proof.
apply ST_Val with (w1:=25). apply v_nat. apply v_nat. 
-apply ST_Prod with (n':=5)( m':=5). reflexivity. apply ST_Refl. apply ST_Refl.
-simpl. apply ST_Prod with (n':=25)( m':=2). simpl. reflexivity. apply ST_Refl. apply ST_Refl.
Qed.

(*Test of fun*)
Lemma bigstep_fun: <{fun prod5 [x:Nat] {x * 5} 5}> ==> 25.
Proof.
apply ST_Fun. simpl.
- apply v_nat.
- apply v_nat.
- simpl. apply ST_Prod with (n':=5)(m':=5). reflexivity. apply ST_Refl. apply ST_Refl.
Qed.

(*Test of fun*)
Lemma bigstep_nv_fun: <{fun prod5 [x:Nat] {(nv_default x) * (nv_default [> 5 ])} ([>5])}> ==> <{25}>.
Proof.
apply ST_Fun. 
-apply v_nvalue.
-apply v_nat.
- simpl. apply ST_Prod with (n':=5)( m':=5).
+ simpl. reflexivity.
+ apply ST_NvDefault with (w:=<{[>5]}>). simpl. reflexivity. apply ST_Refl.
+ apply ST_NvDefault with (w:=<{[>5]}>). simpl. reflexivity. apply ST_Refl.
Qed.


