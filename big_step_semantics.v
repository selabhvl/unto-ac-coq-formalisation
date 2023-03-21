Require Import expression.
Require Import sensor_state.
Require Import value_tree.
Require Import nvalue.
Require Import Bool.
Require Import String.
Require Import List.

Variable Delta : nat.
Variable Sigma : sensor_state.
Variable VtEnvironment : value_tree_env.


Reserved Notation "t '==>' t'" (at level 40).
Inductive bigstep : exp -> exp -> Prop :=
  | ST_Val : forall n t1 t2 w1 w2,
    <{t1}> ==> <{w1}> ->
    <{/n := w1/ t2 }> ==> <{w2}> ->
    <{val n = t1 ; t2}> ==> <{w2}>
  | ST_App : forall v t1 t2' t2 w,
    value v ->
    <{t1}> ==> v ->
    <{t2}> ==> <{t2'}> ->
    <{v t2'}> ==> <{w}> ->
    <{t1 t2}> ==> <{w}>
  | ST_Fun : forall n x T2 t1 v w,
    value v ->
    <{ /n:=(fun n [x:T2] {t1})/ /x:=v/ t1 }> ==> <{w}> ->
    <{(fun n [x:T2] {t1}) v}> ==> <{w}>
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
  | ST_Refl: forall t1, <{t1}> ==> <{t1}>
where "t '==>' t'" := (bigstep t t').
