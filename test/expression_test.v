
From AC Require Import expression.
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
Check <{fun prod5 [x:Nat] {x * [>5]} 5}>.
Check <{x (fun prod5 [x:Nat] {x * 5})}>.
Check <{val n = 25 ; n * 2}>.
Check <{[4 >> 2][5 >> 5][6 >> 4][ > 5]}>.


(*Bounded Test*)
Compute (bounded <{fun fun0 [x:Nat] {x}}>).

Lemma bounded0 : bounded <{fun fun0 [x:Nat] {x}}> nil.
Proof.
simpl. left. reflexivity.
Qed.

Lemma bounded1 : bounded <{fun fun0 [x:Nat] {x * y}}> nil.
Proof.
simpl. split.
-left. reflexivity.
-left.
Abort.

Lemma bounded2 : bounded <{fun fun0 [x:Nat] {x * (fun fun1 [y:Nat] {y})}}> nil.
Proof.
simpl. split.
-left. reflexivity.
-left. reflexivity.
Qed.



