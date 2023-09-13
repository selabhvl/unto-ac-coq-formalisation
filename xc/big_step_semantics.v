From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.

(** Input configuration*)
Inductive conf_in: Type := Input : ident -> sensor_state -> value_tree_env -> exp -> conf_in.
(** Output configuration*)
Inductive conf_out: Type := Output : nvalue -> value_tree -> conf_out.

Notation "<[ id | s | v_env |  ex  ]>" := (Input id s v_env ex).
Notation "<[ w | theta ]>" := (Output w theta).

(** Product operation between literals*)
Definition op_prod (l0:literal) (l1:literal): literal :=
match l0,l1 with
| l_const x, l_const y => l_const (x * y)
| _ , _ => l_fail
end.

(** OR operation between literals*)
Definition op_or (l0:literal) (l1:literal): literal :=
match l0,l1 with
| l_false, l_false=> l_false
| l_true, l_false=> l_true
| l_false, l_true=> l_true
| l_true, l_true=> l_true
| _ , _ => l_fail
end.

(** AND operation between literals*)
Definition op_and (l0:literal) (l1:literal): literal :=
match l0,l1 with
| l_false, l_false=> l_false
| l_true, l_false=> l_false
| l_false, l_true=> l_false
| l_true, l_true=> l_true
| _ , _ => l_fail
end.

(** Single device semantics*)
Reserved Notation "t '==>' t'" (at level 40).
Inductive bigstep : conf_in -> conf_out -> Prop :=

  | E_NVAL : forall (id:ident) (sigma:sensor_state) (env:value_tree_env)  
             (w:nvalue), w_value w -> <[ id | sigma | env | <{w}> ]> ==> <[ <{w}> | empty nil ]> 

  | E_LIT : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (l:literal), value l -> <[ id | sigma | env | <{l}> ]>  ==>  <[ <{[>l]}> | empty nil ]> 

  | E_VAR : forall (id:ident) (sigma:sensor_state) (env:value_tree_env)
            (w:nvalue) x,
            w=(sigma x) ->
            w_value w ->
            <[ id | sigma | env | <{x}> ]>  ==>  <[ <{w}> | empty nil ]> 

  | E_VAL: forall (id:ident) (sigma:sensor_state) (env:value_tree_env)
            x (w1:nvalue) (w2:nvalue) e1 e2 (theta1:value_tree) (theta2:value_tree), 
            <[ id | sigma | pi_env 0 env | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            w_value w1 ->
            <[ id | sigma | pi_env 1 env | <{/x := w1/ e2 }> ]>  ==> <[ <{w2}> | theta2 ]> ->
            w_value w2 ->
            <[ id | sigma | env | <{val x = e1 ; e2}> ]>  ==> <[ <{w2}> | empty (cons theta1 (cons theta2 nil)) ]> 

  | E_APP : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (w0:nvalue) (w1:nvalue) (w2:nvalue) f e0 e1 (theta0:value_tree) (theta1:value_tree) (theta2:value_tree),
            <[ id | sigma | pi_env 0 env  | <{e0}> ]> ==> <[ <{w0}> | theta0 ]> ->
            w_value w0 ->      
            f = (nvalues.get id w0 ) ->
            is_fun f ->  
            <[ id | sigma | pi_env 1 env  | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            w_value w1 ->
            <[ id | sigma | pi_env 2 (select_f env f)  | <{app f $ w1 $}> ]> ==> <[ <{w2}> | theta2 ]> ->
            w_value w2 -> 
            <[ id | sigma | env | <{app e0 $ e1 $}> ]> ==> <[ <{w2}> | some <{[>f]}> (cons theta0 (cons theta1 (cons theta2 nil))) ]>  

  | E_APP_2 : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (w0:nvalue) (w1:nvalue) (w2:nvalue) (w3:nvalue) f e0 e1 e2 (theta0:value_tree) (theta1:value_tree) (theta2:value_tree) (theta3:value_tree),
            <[ id | sigma | pi_env 0 env  | <{e0}> ]> ==> <[ <{w0}> | theta0 ]> ->
            w_value w0 ->      
            f = (nvalues.get id w0 ) ->
            is_fun f ->  
            <[ id | sigma | pi_env 1 env  | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            w_value w1 ->
            <[ id | sigma | pi_env 2 env  | <{e2}> ]> ==> <[ <{w2}> | theta2 ]> ->
            w_value w2 ->
            <[ id | sigma | pi_env 3 (select_f env f)  | <{app f $ w1 w2 $}> ]> ==> <[ <{w3}> | theta3 ]> ->
            w_value w3 -> 
            <[ id | sigma | env | <{app e0 $e1 e2$}> ]> ==> <[ <{w3}> | some <{[>f]}> (cons theta0 (cons theta1 (cons theta2 (cons theta3 nil)))) ]>  

  | E_APP_3 : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (w0:nvalue) (w1:nvalue) (w2:nvalue) (w3:nvalue) (w4:nvalue) f e0 e1 e2 e3 (theta0:value_tree) (theta1:value_tree) (theta2:value_tree) (theta3:value_tree)
            (theta4:value_tree),
            <[ id | sigma | pi_env 0 env  | <{e0}> ]> ==> <[ <{w0}> | theta0 ]> ->
            w_value w0 ->      
            f = (nvalues.get id w0 ) ->
            is_fun f ->  
            <[ id | sigma | pi_env 1 env  | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            w_value w1 ->
            <[ id | sigma | pi_env 2 env  | <{e2}> ]> ==> <[ <{w2}> | theta2 ]> ->
            w_value w2 ->
            <[ id | sigma | pi_env 3 env  | <{e3}> ]> ==> <[ <{w3}> | theta3 ]> ->
            w_value w3 ->
            <[ id | sigma | pi_env 4 (select_f env f)  | <{app f $w1 w2 w3$}> ]> ==> <[ <{w4}> | theta4 ]> ->
            w_value w4 -> 
            <[ id | sigma | env | <{app e0 $e1 e2 e3$}> ]> ==> <[ <{w4}> | some <{[>f]}> (cons theta0 (cons theta1 (cons theta2 (cons theta3 (cons theta4 nil))))) ]>  

  | A_FUN : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (theta:value_tree)
            n x e (w_in:nvalue) (w_out:nvalue),
            w_value w_in ->
            <[ id | sigma | env | <{ /n:=(fun n [x] {e})/ /x:=w_in/ e }> ]> ==> <[ <{w_out}> | theta ]> ->
            w_value w_out ->
            <[ id | sigma | env | <{app (fun n [x] {e}) $ w_in $}> ]> ==> <[  <{w_out}> | theta ]>

  | A_SENS : forall (id:ident) (sigma:sensor_state) (env:value_tree_env)
            (w:nvalue) s, 
            w=(sigma s) -> 
            w_value w -> <[ id | sigma | env | <{sensor s}> ]>  ==>  <[ <{w}> | empty nil ]> 

  | A_SELF :  forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w:nvalue) (l:literal),
            w_value w ->
            l = nvalues.get id w ->
            <[ id | sigma | env | <{app self $ w $}> ]> ==> <[ <{[>l]}> | empty nil ]> 

  | A_UID :  forall (id:ident) (sigma:sensor_state) (env:value_tree_env),
            <[ id | sigma | env | <{uid}> ]> ==> <[ <{[>id]}> | empty nil ]> 

  | A_MULT : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w0:nvalue) (w1:nvalue)  (w2:nvalue) ,
            w_value w0 ->
            w_value w1 ->
            w2=(pointWise op_prod w0 w1) ->
            w_value w2 ->
            <[ id | sigma | env | <{app mult $ w0 w1 $}> ]>  ==> <[ <{w2}> | empty nil ]> 

  | A_OR : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w0:nvalue) (w1:nvalue)  (w2:nvalue) ,
            w_value w0 ->
            w_value w1 ->
            w2=(pointWise op_or w0 w1) ->
            w_value w2 ->
            <[ id | sigma | env | <{app b_or $ w0 w1 $}> ]>  ==> <[ <{w2}> | empty nil ]> 

  | A_AND: forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w0:nvalue) (w1:nvalue)  (w2:nvalue) ,
            w_value w0 ->
            w_value w1 ->
            w2=(pointWise op_and w0 w1) ->
            w_value w2 ->
            <[ id | sigma | env | <{app b_and $ w0 w1 $}> ]>  ==> <[ <{w2}> | empty nil ]> 

  | A_FOLD : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w1:nvalue) (w2:nvalue) (w3:nvalue) (l:literal) (theta:value_tree),
            w_value w1 ->
            w_value w2 ->
            w_value w3 ->
            <[ id | sigma | vt_end | folding id (rev (devices env)) w1 w2 w3 ]> ==> <[ <{[>l]}> | theta ]> -> 
            value l ->
            <[ id | sigma | env | <{app nfold $ w1 w2 w3 $}> ]>  ==> <[ <{[>l]}> | empty nil ]> 

  | A_EXCHANGE : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (theta:value_tree)
                 (w_i:nvalue) (w_f:nvalue) (w_r:nvalue),
            w_value w_i -> 
            w_value w_f ->
            <[ id | sigma | pi_env 0 env  | exp_app_1 w_f (get_messages id w_i env) ]> ==> <[ <{w_r}> | theta ]> ->
            w_value w_r ->            
            <[ id | sigma | env | <{app exchange $w_i w_f$}> ]>  ==> <[ <{w_r}> | some w_r (cons theta nil) ]> 
 
where "t '==>' t'" := (bigstep t t'). 
 




