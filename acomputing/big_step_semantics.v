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
            <[ id | sigma | pi_env 1 env (*TO CHANGE*)| <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            <[ id | sigma | pi_env 2 env (*TO CHANGE*)| <{/x := w1/ e2 }> ]>  ==> <[ <{w2}> | theta2 ]> ->
            <[ id | sigma | env | <{val x = e1 ; e2}> ]>  ==> <[ <{w2}> | empty (cons theta1 (cons theta2 nil)) ]> 

  | E_APP : forall (id:ident) (sigma:sensor_state) (env:value_tree_env) 
            (w0:nvalue) (w1:nvalue) (w2:nvalue) f e0 e1 (theta0:value_tree) (theta1:value_tree) (theta2:value_tree),
            w_value w0 ->
            w_value w1 ->
            w_value w2 ->
            f = (nvalues.get id w0 ) ->
            is_fun f ->
            <[ id | sigma | env (*TO CHANGE*) | <{e0}> ]> ==> <[ <{w0}> | theta0 ]> ->
            <[ id | sigma | env (*TO CHANGE*) | <{e1}> ]> ==> <[ <{w1}> | theta1 ]> ->
            <[ id | sigma | env (*TO CHANGE*)  | <{f w1}> ]> ==> <[ <{w2}> | theta2 ]> ->
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
            <[ id | sigma | env | <{w0 * w1}> ]>  ==> <[ <{w2}> | empty nil ]> 

  (*An implentation of point-wise without FAIL inside nvalue is possible:
      1) extend both w1 w2 with extend function
      2) create a function inside A_PROD that match on w0 w1 w2 and return recursively for
         each position of nvalue or False or (if all locals are natural numbers with same position) 
         l0*l1=l3 /\ (recorsive call) *)



(*

  (*Simplest way, but with FAIL in nvalue literals*)
  | A_MULT : forall e0 e1 (w0:nvalue) (w1:nvalue)  (w2:nvalue) ,
      w_value w0 ->
      w_value w1 ->
      w_value w2 ->
      <{e0}> ==> <{w0}> ->
      <{e1}> ==> <{w1}> ->
      pointWise l_prod w0 w1 ==> <{w2}> ->
      <{e0 * e1}> ==> <{w2}>

  | A_FOLD : forall (l:literal) (w0:nvalue) (w1:nvalue) (w2:nvalue) ,
      w_value w0 ->
      w_value w1 -> 
      w_value w2 -> 
      value l ->
      (*TO DO*) 
      <{nfold w0 w1 w2}> ==> <{[>l]}>  
*)   

  
(*

  | ST_Succ: forall (n:nat) w e, 
    w = S n ->
    <{e}> ==> <{n}> ->
    <{succ e}> ==> <{w}>
  | ST_Pred: forall (n:nat) w e, 
    w = Nat.pred n ->
    <{e}> ==> <{n}> ->
    <{pred e}> ==> <{w}>
  | ST_Prod: forall n (n':nat) m (m':nat) w, 
    w = n' * m' ->
    <{n}> ==> <{n'}> ->
    <{m}> ==> <{m'}> ->
    <{n * m}> ==> <{w}>
  | ST_If_T: forall t1 t2 t3,
    <{t1}> ==> <{true}> ->
    <{if t1 then t2 else t3}> ==> <{t2}>
  | ST_If_F: forall t1 t2 t3,
    <{t1}> ==> <{false}> ->
    <{if t1 then t2 else t3}> ==> <{t3}>
  | ST_Refl: forall t1, <{t1}> ==> <{t1}> *
  | ST_NvGet: forall (n:nat) (w:nvalue literal) e1 e2 (l:literal), 
    l = nvalue.get n w ->
    <{e1}> ==> <{n}> -> 
    <{e2}> ==> <{w}> ->
    <{nv_get e1 e2}> ==> <{l}>
  | ST_NvDefault: forall e1 (l:literal) (w: nvalue literal), *
    l = nvalue.getDefault w ->
    <{e1}> ==> <{w}> ->
    <{nv_default e1}> ==> <{l}> *)
where "t '==>' t'" := (bigstep t t').







