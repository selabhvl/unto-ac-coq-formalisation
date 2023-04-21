Require Import String.
Require Import Bool.
Require Import List.
From AC Require Import syntax.
From AC Require Import nvalues.


(*Not recursive on nvalues*)
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
      if (String.eqb x n) then t else <{val n = (/x:=s/ t1) (*Dentro n non si può sostituire ?*) ; (/x:=s/ t2)}>
  | exp_nvalue w =>
    <{w}>
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
  | l_mult w0 w1 =>
    <{w0 * w1}>
  | l_uid => 
      l_uid
  | l_self w0 =>
      <{self w0 }> 
  | l_sensor s =>
      l_sensor s
  | l_fail => l_fail
  | l_nfold w0 w1 w2 => l_nfold <{/x:=s/ w0}> <{/x:=s/w1}> <{/x:=s/w2}>
  | l_exchange w0 w1 => l_exchange <{/x:=s/w0}> <{/x:=s/w1}>
end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).


(*Recursive on nvalues*)
Fixpoint bounded (e:exp) (l_bounded:list string) {struct e}: Prop :=
let l_b := 
  (fix l_b (l : literal) : Prop := 
        match l with
        | l_uid =>
          True
        | l_self w0 => 
          bounded w0 nil
        | l_sensor s => 
            True
        | l_fail => False
        | <{true}> =>
          False
        | <{false}> =>
          True
        | l_const n =>
          True
        | l_succ t1 =>
          (bounded t1 l_bounded)
        | l_pred t1 =>
          (bounded t1 l_bounded)
        | l_mult w1 w2 =>
            bounded w1 nil /\ bounded w2 nil
        | <{fun n [y:T] {t1}}> =>
            bounded t1 (cons y l_bounded)
        | l_nfold w0 w1 w2 => 
            bounded w0 nil /\ bounded w1 nil /\ bounded w2 nil 
        | l_exchange w0 w1=> 
            bounded w0 nil /\ bounded w1 nil 
        end
    )
in
match e with 
  | exp_var y =>
    In y l_bounded
  | <{fun n [y:T] {t1}}> =>
    bounded t1 (cons y l_bounded)
  | <{t1 t2}> =>
    (bounded t1 l_bounded) /\ (bounded t1 l_bounded)
  | <{val n = t1 ; t2}> =>
    (bounded t1 l_bounded) /\ (bounded t2 (cons n l_bounded))
  | exp_nvalue w =>
    (fix w_rec (w : nvalue ) : Prop := 
    match w with
      | default l => l_b l
      | device _ l wl => l_b l /\ w_rec wl
    end) w
  | exp_literal l => l_b l
end.


Inductive value : literal -> Prop :=
  | v_abs : forall n x T2 t1, bounded <{fun n [x:T2] {t1}}> nil ->
      value <{fun n [x:T2] {t1}}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_nat: forall (n:nat), value <{n}>.
Hint Constructors value : core.

Inductive w_values : nvalue -> Prop :=
| w_default : forall v, value v -> w_values (default v)
| w_device : forall n v wl, value v -> w_values wl -> w_values (device n v wl).

Definition w_value (w:nvalue):= ordered w /\ w_values w.

Inductive is_fun: exp -> Prop :=
  | func : forall n x T2 t1, 
      is_fun <{fun n [x:T2] {t1}}>.





