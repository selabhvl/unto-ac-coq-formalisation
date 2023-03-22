Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Require Import PeanoNat.
Require Import nvalue.
Require Import Bool.
Require Import List.

Inductive ty : Type :=
  | Ty_Builtin : Type -> ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive exp: Type :=
  | exp_var : string -> exp
  | exp_app : exp -> exp -> exp
  | exp_val : string -> exp -> exp -> exp
  | exp_if : exp -> exp -> exp -> exp
  | exp_nvalue : nvalue literal-> exp
  | exp_literal : literal -> exp
with literal :=
  | l_true : literal
  | l_false : literal
  | l_const : nat -> literal
  | l_succ : exp -> literal
  | l_pred : exp -> literal 
  | l_mult : exp -> exp -> literal
  | l_abs : string -> string -> ty -> exp -> literal
  | l_nvalue_get: exp -> exp -> literal
  | l_nvalue_getDefault: exp -> literal.

Declare Custom Entry acnotation.

(*expresion*)
Notation "<{ e }>" := e (e custom acnotation at level 99).

(*variable*)
Coercion exp_var : string >-> exp.

(*lambda*)
Notation "'fun' name [ x :  t ]  { y }" :=
  (l_abs name x t y) (in custom acnotation at level 90, 
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
Notation "'nv_get' pos nv" := (l_nvalue_get pos nv) (in custom acnotation at level 0,
                                     nv custom acnotation at level 0,
                                     pos custom acnotation at level 0).
Notation "'nv_default' x" := (l_nvalue_getDefault x) (in custom acnotation at level 0,
                                     x custom acnotation at level 0).


Coercion exp_literal: literal >-> exp.
Coercion l_const: nat >-> literal.


(*if condition*)
Notation "'if' x 'then' y 'else' z" :=
  (exp_if x y z) (in custom acnotation at level 89,
                    x custom acnotation at level 99,
                    y custom acnotation at level 99,
                    z custom acnotation at level 99,
                    left associativity).

(*nvalues*)
Notation "[ > l ]" := (default literal l) (in custom acnotation at level 30).
Notation "[ x >> y ] m" := ( device literal x y m)(in custom acnotation at level 30,
                                            x at level 99, 
                                            y at level 99, 
                                            m custom acnotation at level 30).

Coercion exp_nvalue: nvalue >-> exp.


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
  | exp_nvalue nv =>
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
  | l_nvalue_get t1 t2 =>
      <{nv_get (/x:=s/ t1) (/x:=s/ t2)}> 
  | l_nvalue_getDefault t1 =>
      <{nv_default (/x:=s/ t1)}> 
  end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).

Fixpoint bounded (e:exp) (l_bounded:list string): Prop :=
match e with 
  | exp_var y =>
    In y l_bounded
  | <{fun n [y:T] {t1}}> =>
    bounded t1 (cons y l_bounded)
  | <{t1 t2}> =>
    (bounded t1 l_bounded) /\ (bounded t1 l_bounded)
  | <{val n = t1 ; t2}> =>
    (bounded t1 l_bounded(*(cons n l_bounded)*)) /\ (bounded t2 (cons n l_bounded))
  | <{if t1 then t2 else t3}> =>
    (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
    /\ (bounded t3 l_bounded)
  | exp_nvalue nv =>
    True
  | <{true}> =>
    False
  | <{false}> =>
    True
  | l_const n =>
    False
  | l_succ t1 =>
    (bounded t1 l_bounded)
  | l_pred t1 =>
    (bounded t1 l_bounded)
  | l_mult t1 t2 =>
    (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
  | l_nvalue_get t1 t2 =>
      (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
  | l_nvalue_getDefault t1 =>
        (bounded t1 l_bounded)
end. 


Inductive value : exp -> Prop :=
  | v_abs : forall n x T2 t1, bounded <{fun n [x:T2] {t1}}> nil ->
      value <{fun n [x:T2] {t1}}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_nat: forall (n:nat), value <{n}>
  | v_nvalue: forall (n:nvalue literal), value <{n}>.
Hint Constructors value : core.

Inductive is_fun: exp -> Prop :=
  | func : forall n x T2 t1, 
      is_fun <{fun n [x:T2] {t1}}>.



