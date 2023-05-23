
From AC Require Import syntax.
From AC Require Import basics.
Require Import String.
Require Import Lia.


(*NOTATION*)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition n : string := "n".
Definition fun0: string := "fun0". 
Definition fun1: string := "fun1". 
Definition prod5: string := "prod5". 

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Check <{x}>.
Check <{fun prod5 [x] {mult (x) ([>5])} 5}>.
Check <{x (fun prod5 [x] {mult (x) (5)})}>.
Check <{val n = 25 ; mult (n) (2)}>.
Check <{[4 >> 2][5 >> 5][6 >> 4][ > 5]}>.


(*Bounded Test*)
Compute (bounded <{fun fun0 [x] {x}}>).

Lemma bounded0 : bounded <{fun fun0 [x] {x}}> nil.
Proof.
simpl. left. reflexivity.
Qed.

Lemma bounded1 : bounded <{fun fun0 [x] {mult x y}}> nil.
Proof.
simpl. split. auto.
Abort.

Lemma bounded2 : bounded <{fun fun0 [x] {mult x (fun fun1 [y] {y})}}> nil.
Proof.
simpl. split.
-auto.
-left. reflexivity.
Qed.



