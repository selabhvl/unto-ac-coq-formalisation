From AC Require Import syntax.
Require Import String. 
Require Import PeanoNat. 
Require Import List. 
Require Import nvalues.

Inductive value_tree: Type :=
| empty : list value_tree -> value_tree
| some : nvalue -> list value_tree  -> value_tree.

Definition rho (v:value_tree) : nvalue :=
match v with 
| empty _ => default l_fail
| some w _ => w
end.

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

Fixpoint devices (env:value_tree_env) : list nat :=
match env with 
| vt_el id _  vl => cons id (devices vl)
| vt_end => nil
end.

Definition name_f (e:exp): option string :=
match e with
| <{fun n[x:T] {m}}> => Some n
| _ => None
end.

Fixpoint select_f (v_env:value_tree_env) (e:exp) : value_tree_env :=
match v_env with
| vt_el id vt v_env_next => match (name_f (nvalues.get id (rho vt) )),(name_f e) with
                            | Some n0, Some n1 => if (String.eqb n0 n1) then 
                                                  (vt_el id vt (select_f v_env_next e)) else
                                                  select_f v_env_next e
                            | _ , _ => select_f v_env_next e (*? OR FAIL*)
                            end
| vt_end => vt_end 
end.

Fixpoint get_messages (my_id:ident) (w_i:nvalue) (v_env:value_tree_env) : nvalue :=
match v_env with
| vt_el id vt v_env_next => device id (nvalues.get my_id (rho vt)) (get_messages my_id w_i v_env_next) 
| v_end => default (nvalues.getDefault w_i) (*nvalue dentro nvalue ?*)
end.
(* Se dentro a un nvalue di un value_tree non è presente 
il valore per il nostro dispositivo è sufficiente il default? *)


Compute (get_messages 2 <{[>5]}> (vt_el 3 (some <{[2>>5][>6]}> nil) 
(vt_el 4 (some <{[1>>2][2>>6][>7]}> nil) (vt_el 7 (some <{[1>>2][2>>6][>7]}> nil) vt_end ) )  )).

Compute (get_messages 2 <{[>5]}> (vt_el 3 (some <{[2>>5][>6]}> nil) 
(vt_el 4 (some <{[1>>2][2>>6][>7]}> nil) (vt_el 7 (empty nil) vt_end ) )  )).







