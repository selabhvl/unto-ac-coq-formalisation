From AC Require Import syntax.
Require Import String. 
Require Import PeanoNat. 
Require Import List. 

Inductive value_tree: Type :=
| empty : list value_tree -> value_tree
| some : nvalue -> list value_tree  -> value_tree.

Definition extract_l (v:value_tree) : list value_tree:= 
match v with 
| empty l => l
| some _ l => l
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

Inductive value_tree_env: Type := 
| vt_el (id:nat) (v1:value_tree) : value_tree_env -> value_tree_env
| vt_end : value_tree_env.

Fixpoint pi_env (pos:nat) (v_env:value_tree_env): value_tree_env :=
match v_env with
| (vt_end) => vt_end
| (vt_el id vt vt_next) => vt_el id (pi pos vt) (pi_env pos vt_next)
end.  











