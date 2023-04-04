From AC Require Import syntax.
From AC Require Import big_step_semantics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import basics.
From AC Require Import nvalues.
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

Lemma multiplication: <[ 10 | base | vt_end |   <{([2>>5][>5]) * ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
apply A_MULT.
-split. apply ordered1. apply w_device. apply v_nat. apply w_default. apply v_nat.
-split. apply ordered1. apply w_device. apply v_nat. apply w_default. apply v_nat.
-split. apply ordered2. auto. apply ordered1. apply w_device. apply v_nat. apply w_device. apply v_nat. apply w_default. apply v_nat.
-simpl. apply E_NVAL. 
split. apply ordered2. auto. apply ordered1. apply w_device. apply v_nat. apply w_device. apply v_nat. apply w_default. apply v_nat.
Qed.