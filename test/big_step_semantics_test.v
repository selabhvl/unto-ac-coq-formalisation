From AC Require Import syntax.
From AC Require Import big_step_semantics.
(* From AC Require Import sensor_state. *)
From AC Require Import value_tree.
From AC Require Import basics.
From AC Require Import nvalues.
From AC Require Import tactics.
Require Import String.

From AC Require Import mapping.
Module BS_Test (M: MAPPING).

  Module Import BS := BigStepSemantics(M).
  Include BS.
  (*NOTATION*)
  Definition x : string := "x".
  Definition y : string := "y".
  Definition z : string := "z".
  Definition n : string := "n".
  Definition fun0: string := "fun0". 
  Definition fun1: string := "fun1". 

  Hint Unfold x : core.
  Hint Unfold y : core.
  Hint Unfold z : core.

  Lemma multiplication: <[ 10 | base_sens | vt_end |   <{app mult $([2>>5][>5]) ([1>>5][>6])$ }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
  Proof. 
  apply A_MULT.
  -split. apply ordered1. simpl. auto.
  -split. apply ordered1. simpl. auto.
  -reflexivity.
  -split. apply ordered2. auto. apply ordered1. simpl. auto.
  Qed.
  
  Lemma fold00: exists w, <[ 4 | base_sens | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $([> fun fun0[x] {fun fun0[y] {app mult $x y$} }]) ([2>>4][3>>5][>6]) ([>7])$}> ]> ==> <[ <{w}> | empty nil ]>.
  Proof.
  eexists.
  device_tac.
  Qed.

End BS_Test.