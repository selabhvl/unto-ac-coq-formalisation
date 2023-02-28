Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

Inductive ty : Type :=
  | Ty_Builtin : Type -> ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm: Type :=
  | tm_var : string -> tm
  | tm_abs :string->string -> ty -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm.

Declare Custom Entry acnotation.

Notation "<{ e }>" := e (e custom acnotation at level 99).
Notation "( x )" := x (in custom acnotation, x at level 99).
Notation "x" := x (in custom acnotation at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom acnotation at level 50, right associativity).
Notation "x y " := (tm_app x y) (in custom acnotation at level 1, left associativity).

Notation "'fun' name [ x :  t ]  { y }" :=
  (tm_abs name x t y) (in custom acnotation at level 90, 
                     x at level 99,
                     t custom acnotation at level 99,
                     y custom acnotation at level 99,
                     name at level 99,
                     left associativity).

Coercion tm_var : string >-> tm.

Notation "'Bool'" := (Ty_Builtin bool) (in custom acnotation at level 0).
Notation "'true'" := true (at level 1).
Notation "'true'" := tm_true (in custom acnotation at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := tm_false (in custom acnotation at level 0).

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
      value <{false}>.

Reserved Notation "'[' x ':=' s ']' t" (in custom acnotation at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{fun n [y:T] {t1}}> =>
      if String.eqb x y then t else <{fun n [y:T] {[x:=s] t1}}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom acnotation).
Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall n x T2 t1 v2,
         value v2 ->
         <{(fun n [x:T2] {t1}) v2}> --> <{ [x:=v2][n:=(fun n [x:T2] {t1})]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1 t2'}>
where "t '-->' t'" := (step t t').


Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Hint Constructors step : core.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


Definition idBf : string := "idB".
Notation idB := <{fun idBf [x:Bool] {x}}>.


Lemma step_example1 :
  <{idB idB}> -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl. Qed.

Definition n : string := "n".

Lemma recursion :
<{(fun n [x:Bool]{n x x}) true }> --> <{(fun n [x:Bool]{n x x}) true true}>.
apply ST_AppAbs. auto.
Qed.

