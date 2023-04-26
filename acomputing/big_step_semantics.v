From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.


Inductive conf_in: Type := Input : ident -> sensor_state -> value_tree_env -> exp -> conf_in.
Inductive conf_out: Type := Output : exp -> value_tree -> conf_out.

Notation "<[ id | s | v_env |  ex  ]>" := (Input id s v_env ex).

Notation "<[ ex | theta ]>" := (Output ex theta).


Definition l_prod (l0:literal) (l1:literal): literal :=
match l0,l1 with
| l_const x, l_const y => l_const (x * y)
| _ , _ => l_fail
end.

Reserved Notation "t '==>' t'" (at level 40).
Inductive bigstep : conf_in -> conf_out -> Prop :=

  | E_NVAL : forall (id:ident) (sigma:sensor_state) (env:value_tree_env)  
             (w:nvalue), w_value w -> <[ id | sigma | env | <{w}> ]> ==> <[ <{w}> | empty nil ]> 

  | E_LIT : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (l:literal), value l -> <[ id | sigma | env | <{l}> ]>  ==>  <[ <{[>l]}> | empty nil ]> 

  | E_VAR : forall (id:ident) (sigma:sensor_state) (env:value_tree_env)
            (w:nvalue) x,
            w_value w ->
            w=(sigma x) -> <[ id | sigma | env | <{x}> ]>  ==>  <[ <{w}> | empty nil ]> 

  | E_VAL: forall (id:ident) (sigma:sensor_state) (env:value_tree_env)
            x (w1:nvalue) (w2:nvalue) e1 e2 (theta1:value_tree) (theta2:value_tree), 
            w_value w1 ->
            w_value w2 ->
            <[ id | sigma | pi_env 0 env | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            <[ id | sigma | pi_env 1 env | <{/x := w1/ e2 }> ]>  ==> <[ <{w2}> | theta2 ]> ->
            <[ id | sigma | env | <{val x = e1 ; e2}> ]>  ==> <[ <{w2}> | empty (cons theta1 (cons theta2 nil)) ]> 

  | E_APP : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (w0:nvalue) (w1:nvalue) (w2:nvalue) f e0 e1 (theta0:value_tree) (theta1:value_tree) (theta2:value_tree),
            w_value w0 ->
            w_value w1 ->
            w_value w2 ->
            f = (nvalues.get id w0 ) ->
            is_fun f ->
            <[ id | sigma | pi_env 0 env  | <{e0}> ]> ==> <[ <{w0}> | theta0 ]> ->
            <[ id | sigma | pi_env 1 env  | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            <[ id | sigma | pi_env 2 (select_f env f)  | <{f w1}> ]> ==> <[ <{w2}> | theta2 ]> ->
            <[ id | sigma | env | <{e0 e1}> ]> ==> <[ <{w2}> | some <{[>f]}> (cons theta0 (cons theta1 (cons theta2 nil))) ]>  

  | A_FUN : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (theta:value_tree)
            n x type e (w_in:nvalue) (w_out:nvalue),
            w_value w_in ->
            w_value w_out ->
            <[ id | sigma | env | <{ /n:=(fun n [x:type] {e})/ /x:=w_in/ e }> ]> ==> <[ <{w_out}> | theta ]> ->
            <[ id | sigma | env | <{(fun n [x:type] {e}) w_in}> ]> ==> <[  <{w_out}> | theta ]>

  | A_SENS : forall (id:ident) (sigma:sensor_state) (env:value_tree_env)
            (w:nvalue) s,
            w_value w ->
            w=(sigma s) -> <[ id | sigma | env | <{sensor s}> ]>  ==>  <[ <{w}> | empty nil ]> 

  | A_SELF :  forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w:nvalue) (l:literal),
            w_value w ->
            l = nvalues.get id w ->
            <[ id | sigma | env | <{self w}> ]> ==> <[ <{l}> | empty nil ]> 

  | A_UID :  forall (id:ident) (sigma:sensor_state) (env:value_tree_env),
            <[ id | sigma | env | <{uid}> ]> ==> <[ <{id}> | empty nil ]> 

  | A_MULT : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w0:nvalue) (w1:nvalue)  (w2:nvalue) ,
            w_value w0 ->
            w_value w1 ->
            w_value w2 ->
            <[ id | sigma | env | (pointWise l_prod w0 w1) ]> ==> <[ <{w2}> | empty nil ]> ->
            <[ id | sigma | env | <{mult w0 w1}> ]>  ==> <[ <{w2}> | empty nil ]> 
  
  | A_FOLD : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (w1:nvalue) (w2:nvalue) (w3:nvalue) (l:literal) (theta:value_tree),
            w_value w1 ->
            w_value w2 ->
            w_value w3 ->
            value l ->
            <[ id | sigma | vt_end | folding id (rev (devices env)) w1 w2 w3 ]> ==> <[ <{[>l]}> | theta ]>   ->
            <[ id | sigma | env | <{nfold w1 w2 w3}> ]>  ==> <[ <{[>l]}> | empty nil ]> 

  | A_EXCHANGE : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) (theta:value_tree)
                 (w_i:nvalue) (w_f:nvalue) (w_r:nvalue),
            w_value w_i -> 
            w_value w_f ->
            w_value w_r ->
            <[ id | sigma | pi_env 0 env  | exp_app w_f (get_messages id w_i env) ]> ==> <[ <{w_r}> | theta ]> ->
            <[ id | sigma | env | <{exchange w_i w_f}> ]>  ==> <[ <{w_r}> | some w_r (cons theta nil) ]> 

where "t '==>' t'" := (bigstep t t').







