

Require Import PeanoNat.
(*an easier notation of this could be defined*)
Inductive nvalue (A:Type):Type:=
| default (n:A) : nvalue A
| device (n:nat) (y:A) : nvalue A -> nvalue A.


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

Check (forall X : Type, X).

(*check*)
Definition int_sum (x:nat) (y:nat) : nat :=  x + y.
Compute(pointWise int_sum (device nat 1 2(device nat 3 5(device nat 5 7(device nat 7 3(default nat 1))))) (device nat 2 2(device nat 4 5(device nat 6 7(device nat 7 3(default nat 2)))))).


(*A nvalue is ordered?*)
Inductive ordered {A} :nvalue A -> Prop :=
| ordered0 : forall x, ordered (default A x)
| ordered1 : forall a0 b0 b1, ordered ((device A a0 b0 (default A b1)))
| ordered2 : forall a0 a1 m b0 b1, lt a0 a1 -> ordered (device A a1 b1 m) -> ordered ((device A a0 b0 (device A a1 b1 m))).


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





