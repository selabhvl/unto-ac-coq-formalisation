From AC Require Import expression.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalue.
Require Import Bool.
Require Import String.
Require Import List.

Variable Delta : nat.
Variable Sigma : sensor_state exp.
Variable VtEnvironment : value_tree_env.

Reserved Notation "t '==>' t'" (at level 40).
Inductive bigstep : exp -> exp -> Prop :=
  | ST_Val : forall x e1 e2 w1 w2,
    value w1 -> 
    value w2 ->
    <{e1}> ==> <{w1}> ->
    <{/x := w1/ e2 }> ==> <{w2}> ->
    <{val x = e1 ; e2}> ==> <{w2}>
  | ST_App : forall f e1 w1 e2 w2,
    is_fun f ->
    <{e1}> ==> f ->
    <{e2}> ==> <{w1}> ->
    <{f w1}> ==> <{w2}> ->
    <{e1 e2}> ==> <{w2}>
  | ST_Fun : forall n x T2 e v w,
    value v ->
    value w ->
    <{ /n:=(fun n [x:T2] {e})/ /x:=v/ e }> ==> <{w}> ->
    <{(fun n [x:T2] {e}) v}> ==> <{w}>
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
  | ST_NvGet: forall (n:nat) (w:nvalue literal) e1 e2 (l:literal), 
    l = nvalue.get n w ->
    <{e1}> ==> <{n}> -> 
    <{e2}> ==> <{w}> ->
    <{nv_get e1 e2}> ==> <{l}>
  | ST_NvDefault: forall e1 (l:literal) (w: nvalue literal),
    l = nvalue.getDefault w ->
    <{e1}> ==> <{w}> ->
    <{nv_default e1}> ==> <{l}>
where "t '==>' t'" := (bigstep t t').






