Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Require Import PeanoNat.
Require Import nvalue.
Require Import value_tree.
Require Import Bool.


Inductive ty : Type :=
  | Ty_Builtin : Type -> ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive exp: Type :=
  | exp_var : string -> exp
  | exp_abs : string -> string -> ty -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_val : string -> exp -> exp -> exp
  | exp_if : exp -> exp -> exp -> exp
  | exp_nvalue (A:Type) : nvalue A -> exp
  | l_true : exp
  | l_false : exp
  | l_const : nat -> exp
  | l_succ : exp -> exp
  | l_pred : exp -> exp 
  | l_mult : exp -> exp -> exp.

Declare Custom Entry acnotation.

(*expresion*)
Notation "<{ e }>" := e (e custom acnotation at level 99).

(*variable*)
Coercion exp_var : string >-> exp.

(*lambda*)
Notation "'fun' name [ x :  t ]  { y }" :=
  (exp_abs name x t y) (in custom acnotation at level 90, 
                     name at level 99,
                     x at level 99,
                     t custom acnotation at level 99,
                     y custom acnotation at level 99,
                     name at level 99,
                     left associativity).

(*application*)
Notation "x y " := (exp_app x y) (in custom acnotation at level 1, left associativity).
Notation "( x )" := x (in custom acnotation, x at level 99).
Notation "x" := x (in custom acnotation at level 0, x constr at level 0).

Notation "'val' name = x ; y" := (exp_val name x y) (in custom acnotation at level 90,
                                                    name at level 99,
                                                    x custom acnotation at level 99,
                                                    y custom acnotation at level 99,
                                                    left associativity).

Notation "S -> T" := (Ty_Arrow S T) (in custom acnotation at level 50, right associativity).

(*boolean*)
Notation "'Bool'" := (Ty_Builtin bool) (in custom acnotation at level 0).
Notation "'true'" := true (at level 1).
Notation "'true'" := l_true (in custom acnotation at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := l_false (in custom acnotation at level 0).

(*natural numbers*)
Notation "'Nat'" := (Ty_Builtin nat) (in custom acnotation at level 0).
Notation "'succ' x" := (l_succ x) (in custom acnotation at level 0,
                                     x custom acnotation at level 0).
Notation "'pred' x" := (l_pred x) (in custom acnotation at level 0,
                                     x custom acnotation at level 0).
Notation "x * y" := (l_mult x y) (in custom acnotation at level 1,
                                      left associativity).
Coercion l_const: nat >-> exp.

(*if condition*)
Notation "'if' x 'then' y 'else' z" :=
  (exp_if x y z) (in custom acnotation at level 89,
                    x custom acnotation at level 99,
                    y custom acnotation at level 99,
                    z custom acnotation at level 99,
                    left associativity).

(*nvalues*)
Notation "[ > l ]" := (default _ l) (in custom acnotation at level 30).
Notation "[ x >> y ] m" := ( device _ x y m)(in custom acnotation at level 30,
                                            x at level 99, 
                                            y at level 99, 
                                            m custom acnotation at level 30).

Coercion exp_nvalue: nvalue >-> exp.
Notation "'NvalueNat'" := (Ty_Builtin (nvalue nat)) (in custom acnotation at level 0).


Inductive value : exp -> Prop :=
  | v_abs : forall n x T2 t1,
      value <{fun n [x:T2] {t1}}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_nat: forall (n:nat), value <{n}>
  | v_nvalue: forall (A:Type) (n:nvalue A), value <{n}>.

Reserved Notation "'/' x ':=' s '/' t" (in custom acnotation at level 20, x constr).
Fixpoint subst (x : string) (s : exp) (t : exp) : exp :=
  match t with
  | exp_var y =>
      if String.eqb x y then s else t
  | <{fun n [y:T] {t1}}> =>
      if ((String.eqb x y) || (String.eqb x n)) then t else <{fun n [y:T] {/x:=s/ t1}}>
  | <{t1 t2}> =>
      <{(/x:=s/ t1) (/x:=s/ t2)}>
  | <{val n = t1 ; t2}> =>
      if (String.eqb x n) then t else <{val n = (/x:=s/ t1) ; (/x:=s/ t2)}>
  | <{if t1 then t2 else t3}> =>
        <{if (/x:=s/ t1) then (/x:=s/ t2) else (/x:=s/ t3)}>
  | exp_nvalue x nv =>
    <{nv}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | l_const n =>
    <{n}>
  | l_succ t1 =>
    <{succ (/x:=s/ t1)}>
  | l_pred t1 =>
    <{pred (/x:=s/ t1)}>
  | l_mult t1 t2 =>
    <{(/x:=s/ t1) * (/x:=s/ t2)}>
  end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).
Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40). 
Inductive step : exp -> exp -> Prop :=
  | ST_AppAbs : forall n x T2 t1 v2,
         value v2 ->
         <{(fun n [x:T2] {t1}) v2}> --> <{ /n:=(fun n [x:T2] {t1})/ /x:=v2/ t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_succ: forall (n:nat) (m:nat), m = S n -> <{succ n}> --> <{m}>
  | ST_succ_step: forall t t',  t --> t' -> <{succ t}> --> <{succ t'}>
  | ST_pred: forall (n:nat) (m:nat), m = Nat.pred n -> <{pred n}> --> <{m}>
  | ST_pred_step: forall t t',  t --> t' -> <{pred t}> --> <{pred t'}>
  | ST_prod: forall (n:nat) (m:nat) (r:nat), r = n * m -> <{n * m}> --> <{r}>
  | ST_prod_left: forall (n:nat) (n':nat) (m:nat), n --> n' -> <{n * m}> --> <{n' * m}>
  | ST_prod_right: forall (n:nat) (m:nat) (m':nat), m --> m' -> <{n * m}> --> <{n * m'}>
  | ST_Let1: forall n t1 t1' t2, t1 --> t1' -> 
            <{val n = t1 ; t2}> --> <{val n = t1' ; t2}>
  | ST_LetValue: forall n v1 t2, value v1 -> <{val n = v1 ; t2}> --> <{ /n:=v1/t2}>
where "t '-->' t'" := (step t t').

(*multi-step*)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_single : forall (x y: X), R x y -> multi R x y
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


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


