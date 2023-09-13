From AC Require Import syntax.
Require Import String. 
Require Import PeanoNat. 
Require Import List. 
Require Import nvalues.

(** Value tree is formalized as a tree that can contain a nvalue as root value*)
Inductive value_tree: Type :=
| empty : list value_tree -> value_tree
| some : nvalue -> list value_tree  -> value_tree.

(** Return the value in the root if exists*)
Definition rho (v:value_tree) : option nvalue :=
match v with 
| empty _ => None
| some w _ => Some w
end.

(** Return the childs of a value tree*)
Definition extract_l (v:value_tree) : list value_tree:= 
match v with 
| empty l => l
| some _ l => l
end.

(** Return the child in position 'pos' if exists, empty nill otherwise*)
Fixpoint pi (pos:nat) (v:value_tree): value_tree :=
let ll := extract_l v in 
match pos , ll with
| (S n) ,(cons _ l) => pi n (empty l)
| 0 , (cons vt _) => vt
| (S n) , (nill) => empty nill
| 0 , (nill) => empty nill
end.

(** Inductive definition of value tree environment*)
Inductive value_tree_env: Type := 
| vt_el (id:ident) (v1:value_tree) : value_tree_env -> value_tree_env
| vt_end : value_tree_env.

(** Function pi applied to all elements of an environment*)
Fixpoint pi_env (pos:nat) (v_env:value_tree_env): value_tree_env :=
match v_env with
| (vt_end) => vt_end
| (vt_el id vt vt_next) => vt_el id (pi pos vt) (pi_env pos vt_next)
end.  

(** Returns the device involved in an environment*)
Fixpoint devices (env:value_tree_env) : list nat :=
match env with 
| vt_el id _  vl => cons id (devices vl)
| vt_end => nil
end.

(** Return the name of a function*)
Definition name_f (e:exp): option string :=
match e with
| <{fun n[x] {m}}> => Some n
| <{exchange}> => Some "exchange"%string
| <{nfold}> => Some "nfold"%string
| <{self}> => Some "self"%string
| <{uid}> => Some "uid"%string
| <{succ}> => Some "succ"%string
| <{pred}> => Some "pred"%string
| <{mult}> => Some "mult"%string
| <{b_or}> => Some "b_or"%string
| <{b_and}> => Some "b_and"%string
| _ => None
end.


(** Select only the value trees of an environment
that containt a certain function in the root*)
Fixpoint select_f (v_env:value_tree_env) (e:exp) : value_tree_env :=
match v_env with
| vt_el id vt v_env_next => match (rho vt) with
                            | None => select_f v_env_next e 
                            | Some w => match (name_f (nvalues.get id (w) )),(name_f e) with
                                        | Some n0, Some n1 => if (String.eqb n0 n1) then 
                                                              (vt_el id vt (select_f v_env_next e)) else
                                                              select_f v_env_next e
                                        | _ , _ => select_f v_env_next e 
                                        end 
                            end
| vt_end => vt_end 
end.

(** Return the messages sended to a certain id in a vt env*)
Fixpoint get_messages (my_id:ident) (w_i:nvalue) (v_env:value_tree_env) : nvalue :=
match v_env with
| vt_el id vt v_env_next => match (rho vt) with
                            | Some w => device id (nvalues.get my_id (w)) (get_messages my_id w_i v_env_next) 
                            | None => (get_messages my_id w_i v_env_next)
                            end
| v_end => default (nvalues.getDefault w_i)
end.




