Require Import PeanoNat.
From AC Require Import syntax.
From AC Require Import nvalues.


Compute (get 0 <{[0>>6][>5]}>).
Compute (get 1 <{[0>>6][>5]}>).
Compute (get 2 <{[0>>6][2>>7][>5]}>).
Compute (getDefault <{[0>>6][2>>7][>5]}>).

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

Compute (extend (device 1 2 (device 5 4 (device 7 6 (default 8))))  
(device 0 1 (device 1 3 (device 3 5 (device 4 7 (device 5 9 (device 6 11 ( device 8 13 ((default 6)))))))))).

Compute (extend (device  1 2(device  3 5(device  5 7(device  7 3(default  1))))) (device  2 2 (device  4 5(device  6 7(device  7 3 (default  2)))))).

Compute (extend (device  2 2(device  4 5(device  6 7(device  7 3(default  2)))))  (device  1 2(device  3 5(device  5 7(device  7 3 (default  1)))))).

