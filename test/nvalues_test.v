Require Import PeanoNat.
From AC Require Import syntax.
From AC Require Import nvalues.
From AC Require Import value_tree.
Require Import String.
Require Import List.

Definition x : string := "x".
Definition y : string := "y".
Definition fun0: string := "fun0". 
Definition fun1: string := "fun1".

Compute (nvalues.get 0 <{[0>>6][>5]}>).
Compute (nvalues.get 1 <{[0>>6][>5]}>).
Compute (nvalues.get 2 <{[0>>6][2>>7][>5]}>).
Compute (nvalues.getDefault <{[0>>6][2>>7][>5]}>).

Lemma first: ordered (default 5).
Proof.
apply ordered0.
Qed.

Lemma second: ordered(device 3 5(default 4)).
Proof.
apply ordered1.
Qed.

Lemma third: ordered(device 2 5(device 3 5(default 4))).
Proof.
apply ordered2. apply Nat.lt_succ_diag_r. apply ordered1.
Qed.

Definition l_sum (x:literal) (y:literal) : literal := match x,y with | l_const x, l_const y => l_const (x+y) | _ , _ => l_fail end.
Compute(pointWise l_sum (device  1 2(device  3 5(device  5 7(device  7 3(default  1))))) (device  2 2(device  4 5(device  6 7(device  7 3 (default  2)))))).

Compute (folding 4 (rev (devices (vt_el 4 (empty nil) (vt_el 5 (empty nil) vt_end)))) <{[ > fun fun0[x] {fun fun0[y] {app mult $x y$} }]}>  <{[4 >> 2][5 >> 6][> 7]}> <{[>6]}> ).