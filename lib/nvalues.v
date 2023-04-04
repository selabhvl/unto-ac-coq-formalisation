Require Import PeanoNat.
From AC Require Import syntax.

(*get single device value*)
Fixpoint get (pos:ident) (n:nvalue): literal :=
match n with
| default  x => x
| device i x m => if (pos=?i) then x else (get pos m)
end.

Fixpoint getDefault (n:nvalue): literal :=
match n with
| default x => x
| device i x m => getDefault m
end.

(*ordered predicate*)
Inductive ordered :nvalue -> Prop :=
| ordered0 : forall x, ordered (default x)
| ordered1 : forall a0 b0 b1, ordered ((device a0 b0 (default b1)))
| ordered2 : forall a0 a1 m b0 b1, lt a0 a1 -> ordered (device a1 b1 m) -> ordered ((device a0 b0 (device a1 b1 m))).


Fixpoint pointWise (op:literal -> literal -> literal) (w0:nvalue) {struct w0}: nvalue -> nvalue:=
fix pointWise1 (w1:nvalue) {struct w1}: nvalue :=
match w0,w1 with
| default x , default y => default (op x y)
| default x , device a b m  =>  device a (op x b) (pointWise1 m) 
| device a b m , default x  => device a (op x b) (pointWise op  m (default x)) 
| device a0 b0 m0 , device a1 b1 m1  => if (a0=?a1) then device a0 (op b0 b1) (pointWise op m0 m1)
                                            else (if (a0<?a1) then device a0 (op b0 (getDefault m1)) (pointWise op m0 (device a1 b1 m1))
                                            else device a1 (op (getDefault m0) b1) (pointWise1 m1 ))
end.

Fixpoint extend (w0:nvalue) {struct w0}: nvalue -> nvalue:=
fix extend1 (w1:nvalue) {struct w1}: nvalue :=
match w0,w1 with
| default x , default y => default x
| default x , device a b m  =>  device a x (extend1 m) 
| device a b m , default x  => device a b (extend m w1)
| device a0 b0 m0 , device a1 b1 m1  => if (a0=?a1) then device a0 b0 (extend m0 m1)
                                            else (if (a0<?a1) then device a0 b0 (extend m0 w1)
                                            else device a1 (getDefault w0) (extend1 m1))
end. 



(*
Compute (extend (device nat 1 2 (device nat 5 4 (device nat 7 6 (default nat 8))))  
(device nat 0 1 (device nat 1 3 (device nat 3 5 (device nat 4 7 (device nat 5 9 (device nat 6 11 ( device nat 8 13 ((default nat 6)))))))))).


Fixpoint defaultV {A} (n:nvalue A): A :=
match n with
| default _ x => x
| device _ _ _ m => defaultV m
end.
(*Operation between two nvalues*)
(*A is the type of nvalue, op is the point-wise operation*)
(*nvalues need to be ordered, this is achieved by a properly insertion in the data type*)
(*It's possible to define a pointwise operation on non order nvalues,
but we must to assure that the nvalue don't contains duplicates*)
Fixpoint pointWise {A} (op:A->A->A) (w0:nvalue A) {struct w0}: nvalue A -> nvalue A:=
fix pointWise1 (w1:nvalue A) {struct w1}: nvalue A :=
match w0,w1 with
| default _ x , default _ y => default A (op x y)
| default _ x , device _ a b m  =>  device A a b (pointWise1 m) 
| device _ a b m , default _ x  => device A a b (pointWise op  m (default A x)) 
| device _ a0 b0 m0 , device _ a1 b1 m1  => if (a0=?a1) then device A a0 (op b0 b1) (pointWise op m0 m1)
                                            else (if (a0<?a1) then device A a0 (op b0 (defaultV m1)) (pointWise op m0 (device A a1 b1 m1))
                                            else device A a1 (op (defaultV m0) b1) (pointWise1 m1 ))
end.


(*check*)
Definition int_sum (x:nat) (y:nat) : nat :=  x + y.
Compute(pointWise int_sum (device nat 1 2(device nat 3 5(device nat 5 7(device nat 7 3(default nat 1))))) (device nat 2 2(device nat 4 5(device nat 6 7(device nat 7 3(default nat 2)))))).




Lemma first: ordered (default nat 5).
Proof.
apply ordered0.
Qed.

Lemma second: ordered(device nat 3 5(default nat 4)).
Proof.
apply ordered1.
Qed.

Search lt.
Lemma third: ordered(device nat 2 5(device nat 3 5(default nat 4))).
Proof.
apply ordered2. apply Nat.lt_succ_diag_r. apply ordered1.
Qed.
*)


