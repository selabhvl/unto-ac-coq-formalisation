Require Import String. 
Require Import nvalue. 
Require Import PeanoNat. 

Inductive value_tree: Type :=
| empty : list0 -> value_tree
| some (B:Type) (A:nvalue B): list0  -> value_tree
with list0 :=
| nill : list0
| cons : value_tree -> list0 -> list0.

Definition extract_l (v:value_tree) : list0:= 
match v with 
| empty l => l
| some _ _ l => l
end.

(*return empty value_tree if pos dowsn't exists*)
Fixpoint pi (pos:nat) (v:value_tree): value_tree :=
let ll := extract_l v in 
match pos , ll with
| (S n) ,(cons _ l) => pi n (empty l)
| 0 , (cons vt _) => vt
| (S n) , (nill) => empty nill
| 0 , (nill) => empty nill
end.














