From AC Require Import basics.
From AC Require Import nvalues.
From AC Require Import syntax.
From AC Require Import basics.
Require Import String.


Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition n : string := "n".
Definition fun0: string := "fun0". 
Definition fun1: string := "fun1". 
Definition prod5: string := "prod5". 

Check <{x}>.
Check <{fun prod5 [x:Nat] {x * [>5]} 5}>.
Check <{x (fun prod5 [x:Nat] {x * 5})}>.
Check <{val n = 25 ; n * 2}>.
Check <{[4 >> 2][5 >> 5][6 >> 4][ > 5]}>.
Check <{uid}>.
Check <{self [>6]}>.
Check <{sensor x}>.
Check <{FAIL}>.
Check <{nfold [> fun fun1 [x:Nat] {fun fun0  [y:Nat] {x}} ] [0 >> 5][1 >> 3][ > 4 ] [> 5]}>.


Compute (<{/x:=5/ (x * y)}>).

Compute (<{ /y:=10/ fun prod5 [x:Nat] {x * y * [>5]} 5}>).

Compute <{/x:=4/ (x (fun prod5 [x:Nat] {x * 5}))}>.

Compute <{/prod5:=4/ (x (fun prod5 [x:Nat] {x * 5}))}>.

Compute (bounded <{x}> nil).

Lemma test1 : bounded <{fun fun0 [x:Nat] {x} }> nil.
Proof.
simpl. auto.
Qed.

Lemma test2 : bounded <{[0 >> 5][>5]}> nil.
Proof.
simpl. auto.
Qed.

Lemma test3 : bounded <{[0 >> (fun fun0 [x:Nat] {x})][>5]}> nil.
Proof.
simpl. split. left. auto. auto. 
Qed.

Lemma test4 : bounded <{[0 >> (fun fun0 [x:Nat] {x*y})][>5]}> nil.
Proof.
simpl. split. split. auto. 
Abort.

Lemma test4 : bounded <{nfold [0 >> (fun fun0 [x:Nat] {x*y})][>5] [>6] [>([>1] * [>(fun fun0 [x:Nat] {y})])] }> nil.
Proof.
simpl. split. split. split. auto. 
Abort.

Lemma w_test0 : w_value <{[>3]}>.
Proof.
split. apply ordered0. apply w_default. apply v_nat.
Qed.

Lemma w_test1 : w_value <{[3 >> 2][2 >> 4][>3]}>.
Proof.
split. apply ordered2. 
Abort.

Lemma w_test2 :  w_value <{[1 >> (fun fun0 [x:Nat] {y})][2 >> 4][>3]}>.
Proof.
split. 
- apply ordered2. auto. apply ordered1. 
- apply w_device.
+ apply v_abs. simpl. left. 
Abort.

