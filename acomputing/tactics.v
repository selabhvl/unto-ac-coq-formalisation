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

Ltac ordered_tac := first [apply ordered0 | apply ordered1 | apply ordered2;auto;ordered_tac].
Ltac w_tac := split; [>ordered_tac | simpl;auto].

Ltac mult_tac  := 
apply A_MULT;
match goal with
| [|- w_value ?X] => w_tac
| _ => apply E_NVAL; w_tac
end.

Lemma multiplication: <[ 10 | base | vt_end |   <{mult ([1>>5][2>>5][>5]) ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
mult_tac.
Qed.