Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Require Import PeanoNat.
Require Import nvalue.


Inductive ty : Type :=
  | Ty_Builtin : Type -> ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm: Type :=
  | tm_var : string -> tm
  | tm_abs :string->string -> ty -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if0 : tm -> tm -> tm -> tm
  | tm_const : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm 
  | tm_mult : tm -> tm -> tm
  | tm_nvalue (A:Type) : nvalue A -> tm.

Declare Custom Entry acnotation.

(*expresion*)
Notation "<{ e }>" := e (e custom acnotation at level 99).

(*variable*)
Coercion tm_var : string >-> tm.

(*lambda*)
Notation "'fun' name [ x :  t ]  { y }" :=
  (tm_abs name x t y) (in custom acnotation at level 90, 
                     name at level 99,
                     x at level 99,
                     t custom acnotation at level 99,
                     y custom acnotation at level 99,
                     name at level 99,
                     left associativity).

(*application*)
Notation "x y " := (tm_app x y) (in custom acnotation at level 1, left associativity).
Notation "( x )" := x (in custom acnotation, x at level 99).
Notation "x" := x (in custom acnotation at level 0, x constr at level 0).

Notation "S -> T" := (Ty_Arrow S T) (in custom acnotation at level 50, right associativity).

(*boolean*)
Notation "'Bool'" := (Ty_Builtin bool) (in custom acnotation at level 0).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom acnotation at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom acnotation at level 0).

(*natural numbers*)
Notation "'Nat'" := (Ty_Builtin nat) (in custom acnotation at level 0).
Notation "'succ' x" := (tm_succ x) (in custom acnotation at level 0,
                                     x custom acnotation at level 0).
Notation "'pred' x" := (tm_pred x) (in custom acnotation at level 0,
                                     x custom acnotation at level 0).
Notation "x * y" := (tm_mult x y) (in custom acnotation at level 1,
                                      left associativity).
Coercion tm_const: nat >-> tm.

(*if condition*)
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom acnotation at level 89,
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
(* <{ [5 >> 6] [5 >> 9] [ > 6 ]}> *)
(* <{ [id   value] [id   value] [default] }> *)
Coercion tm_nvalue: nvalue >-> tm.
Notation "'NvalueNat'" := (Ty_Builtin (nvalue nat)) (in custom acnotation at level 0).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Inductive value : tm -> Prop :=
  | v_abs : forall n x T2 t1,
      value <{fun n [x:T2] {t1}}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_nat: forall (n:nat), value <{n}>.

Reserved Notation "'/' x ':=' s '/' t" (in custom acnotation at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{fun n [y:T] {t1}}> =>
      if String.eqb x y then t else <{fun n [y:T] {/x:=s/ t1}}>
  | <{t1 t2}> =>
      <{(/x:=s/ t1) (/x:=s/ t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if0 t1 then t2 else t3}> =>
      <{if0 (/x:=s/ t1) then (/x:=s/ t2) else (/x:=s/ t3)}>
  | tm_const n =>
    <{n}>
  | tm_succ t1 =>
    <{succ (/x:=s/ t1)}>
  | tm_pred t1 =>
    <{pred (/x:=s/ t1)}>
  | tm_mult t1 t2 =>
    <{(/x:=s/ t1) * (/x:=s/ t2)}>
  | tm_nvalue x nv =>
    <{nv}>
  end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).
Hint Constructors value : core.


Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
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
      <{if0 true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if0 false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if0 t1 then t2 else t3}> --> <{if0 t1' then t2 else t3}>
  | ST_succ: forall (n:nat) (m:nat), m = S (n) -> <{succ n}> --> <{m}>
  | ST_pred: forall (n:nat) (m:nat), m = Nat.pred n -> <{pred n}> --> <{m}>
  | ST_prod: forall (n:nat) (m:nat) (r:nat), r = n * m -> <{n * m}> --> <{r}>
where "t '-->' t'" := (step t t').


