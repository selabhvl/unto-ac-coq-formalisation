From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.


(*It's beter to replace auto with apropriate basic tactic*)
Ltac ordered_tac := solve [apply ordered0 | apply ordered1 | apply ordered2;auto;ordered_tac].
Ltac w_tac := solve [split; [>ordered_tac | simpl;auto]].

Ltac nval_tac := solve [apply E_NVAL; w_tac].

Ltac lit_tac := solve [apply E_LIT; unfold value; simpl; auto].

Ltac var_tac := 
apply E_VAR;
[>w_tac|
unfold base; repeat (unfold add); simpl;
lazymatch goal with 
| [|- context [l_fail]]=> fail
| _ => reflexivity
end].

Ltac mult_tac  := 
solve [apply A_MULT;
match goal with
| [|- w_value ?X] => w_tac
| _ => nval_tac
end].



Definition x:string := "x".
Definition y:string := "y".
Definition z:string := "z".
Definition fun0:string := "fun0".

Lemma mult: <[ 10 | base | vt_end |   <{mult ([1>>5][2>>5][>5]) ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
mult_tac.
Qed.

Lemma wrong_mult: <[ 10 | base | vt_end |   <{mult ([2>>5][2>>5][>5]) ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
try mult_tac.
Abort.

Lemma lit: <[ 10 | base | vt_end |   <{ 5 }> ]> ==> <[ <{[>5]}> | empty nil ]>.
Proof.
lit_tac.
Qed.

Lemma wrong_lit: <[ 10 | base | vt_end |   <{ fun fun0[x:Nat]{mult x y} }> ]> ==> <[ <{[>fun fun0[x:Nat]{mult x y}]}> | empty nil ]>.
Proof.
try lit_tac.
Abort.

Lemma var: <[10 | add y <{[>5]}> (add x <{[>6]}> base) | vt_end | <{y}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
var_tac.
Qed.

Lemma wrong_var: <[10 | add y <{[>5]}> (add y <{[>6]}> base) | vt_end | <{z}> ]> ==> <[ <{[>FAIL]}> | empty nil  ]>.
Proof.
try var_tac.
Abort.





