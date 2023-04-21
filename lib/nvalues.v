Require Import PeanoNat.
From AC Require Import syntax.
Require Import List.

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



Fixpoint folding (delta:ident) (devs:list nat) (w1:nvalue) (w2:nvalue) (w3:nvalue) : exp :=
match devs with 
| cons id l => if (delta =? id) then (folding id l w1 w2 w3) else exp_app (exp_app w1 (nvalues.get id w2)) (folding delta l w1 w2 w3)
| nil => (get delta w3)
end.


