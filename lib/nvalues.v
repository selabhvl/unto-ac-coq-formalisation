Require Import PeanoNat.
From AC Require Import syntax.
Require Import List.

(** Get the value of the device 'pos'*)
Fixpoint get (pos:ident) (n:nvalue): literal :=
match n with
| default  x => x
| device i x m => if (pos=?i) then x else (get pos m)
end.

(** Return the default value of a nvalue*)
Fixpoint getDefault (n:nvalue): literal :=
match n with
| default x => x
| device i x m => getDefault m
end.

(** ordered predicate: a nvalue is ordered if the device id are 
listed in strictly positive order*)
Inductive ordered :nvalue -> Prop :=
| ordered0 : forall x, ordered (default x)
| ordered1 : forall a0 b0 b1, ordered ((device a0 b0 (default b1)))
| ordered2 : forall a0 a1 m b0 b1, lt a0 a1 -> ordered (device a1 b1 m) -> ordered ((device a0 b0 (device a1 b1 m))).

(** apply the operation 'op' to two nvalues matching device id*)
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

Definition isBuiltin (id:ident) (w:nvalue) := 
match (nvalues.get id w) with
| l_builtin b=> true
| _ => false
end.

(** Return a expression that apply the function in 'w1' for the neighbours values in w2*)
Fixpoint folding (delta:ident) (devs:list nat) (w1:nvalue) (w2:nvalue) (w3:nvalue) : exp :=
match devs with 
| cons id l => if (delta =? id) then (folding id l w1 w2 w3) else 
                          (if (isBuiltin delta w1) 
                           then exp_app_2 w1 (nvalues.get id w2) (folding delta l w1 w2 w3) 
                           else exp_app_1 (exp_app_1 w1 (nvalues.get id w2)) (folding delta l w1 w2 w3) )
| nil => (get delta w3)
end.


