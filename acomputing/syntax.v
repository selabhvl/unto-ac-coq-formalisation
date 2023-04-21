(** ** SYNTAX 
    In this section we define the syntax of the aggregate computing calculus
    The syntax, as for the semantics, is similar to the lambda calculus.
*)


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Import Strings.String.
Require Import PeanoNat.
Require Import Bool.
Require Import List.

(** The identifier of a device is seen as natural number*)
Definition ident := nat.

Inductive ty : Type :=
  | Ty_Builtin : Type -> ty
  | Ty_Arrow : ty -> ty -> ty.

(** SYNTAX of an EXPRESSION, including LITERALS and NVALUES*)
(** An expression can be a 
variable (rappresented by string), .... *)
Inductive exp: Type :=
  | exp_var : string -> exp
  | exp_app : exp -> exp -> exp
  | exp_val : string -> exp -> exp -> exp
  | exp_nvalue : nvalue -> exp
  | exp_literal : literal -> exp
with literal :=
  | l_self: exp -> literal
  | l_uid: literal
  | l_sensor: string -> literal
  | l_fail : literal
  | l_true : literal
  | l_false : literal
  | l_const : nat -> literal
  | l_succ : exp -> literal
  | l_pred : exp -> literal 
  | l_abs : string -> string -> ty -> exp -> literal 
  | l_mult : exp -> exp -> literal
  | l_nfold : exp -> exp -> exp -> literal
  | l_exchange : exp -> exp -> literal
with nvalue :=
  | default: literal -> nvalue
  | device (n:ident) : literal -> nvalue -> nvalue.

Declare Custom Entry acnotation.

(** In order to make an expresion more undestandable we define a notation for syntax, including
nvalues*)
Notation "<{ e }>" := e (e custom acnotation at level 99).

Notation "'fun' name [ x :  t ]  { y }" :=
  (l_abs name x t y) (in custom acnotation at level 90, 
                     name at level 99,
                     x at level 99,
                     t custom acnotation at level 99,
                     y custom acnotation at level 99,
                     name at level 99,
                     left associativity).

Notation "x y " := (exp_app x y) (in custom acnotation at level 1, left associativity).
Notation "( x )" := x (in custom acnotation, x at level 99).
Notation "x" := x (in custom acnotation at level 0, x constr at level 0).

Notation "'val' name = x ; y" := (exp_val name x y) (in custom acnotation at level 90,
                                                    name at level 99,
                                                    x custom acnotation at level 99,
                                                    y custom acnotation at level 99,
                                                    left associativity).

Notation "S -> T" := (Ty_Arrow S T) (in custom acnotation at level 50, right associativity).

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

Notation "'nfold' e0 e1 e2" := (l_nfold e0 e1 e2) (in custom acnotation at level 0,
                                     e0 custom acnotation at level 0,
                                     e1 custom acnotation at level 0,
                                     e2 custom acnotation at level 0).

Notation "'exchange' e0 e1" := (l_exchange e0 e1) (in custom acnotation at level 0,
                                     e0 custom acnotation at level 0,
                                     e1 custom acnotation at level 0).


(*nvalues*)
Notation "[ > l ]" := (default l) (in custom acnotation at level 30).
Notation "[ x >> y ] m" := ( device x y m)(in custom acnotation at level 30,
                                            x at level 99, 
                                            y at level 99, 
                                            m custom acnotation at level 30).

Notation "'FAIL'" := (l_fail) (in custom acnotation at level 0).

Notation "'sensor' x" := (l_sensor x) (in custom acnotation at level 0, x custom acnotation at level 0).

Notation "'self' x" := (l_self x) (in custom acnotation at level 0, x custom acnotation at level 0).

Notation "'uid'" := (l_uid) (in custom acnotation at level 0).

(** EXPRESS CONCEPT*)
Coercion exp_var : string >-> exp.
Coercion exp_literal: literal >-> exp.
Coercion l_const: nat >-> literal.
Coercion exp_nvalue: nvalue >-> exp.
