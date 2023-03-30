From AC Require Import expression.

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
Inductive multi (X : Type) (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi X R x x
  | multi_single : forall (x y: X), R x y -> multi X R x y
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Notation multistep := (multi exp step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).