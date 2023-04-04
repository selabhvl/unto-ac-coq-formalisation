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
      <{nv_get t1 t2}> 
  | l_nvalue_getDefault t1 =>
      <{nv_default t1}> 
  | l_uid => 
      l_uid
  | l_self e0 =>
      <{self e0 }> 
  | l_sensor s =>
      l_sensor s
  | l_fail => l_fail
  | l_nfold e0 e1 e2 => l_nfold e0 e1 e2
end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).

(*
(*Recursive on nvalues*)
Reserved Notation "'/' x ':=' s '/' t" (in custom acnotation at level 20, x constr).
Fixpoint subst (x : string) (s : exp) (t : exp) : exp := 
let l_s := 
  (fix l_s (l : literal) : literal := 
        match l with
          | l_uid => 
            l_uid
          | l_self e0 =>
            <{self (/x:=s/ e0) }> 
          | l_sensor s =>
            l_sensor s
          | l_fail => l_fail
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
          | <{fun n [y:T] {t1}}> =>
            if ((String.eqb x y) || (String.eqb x n)) then l else <{fun n [y:T] {/x:=s/ t1}}>
          | l_nfold e0 e1 e2 =>
            <{nfold (/x:=s/ e0) (/x:=s/ e1) (/x:=s/ e2)}>
        end)
in
  match t with
  | exp_var y =>
      if String.eqb x y then s else t
    | <{t1 t2}> =>
      <{(/x:=s/ t1) (/x:=s/ t2)}>
  | <{val n = t1 ; t2}> =>
      if (String.eqb x n) then t else <{val n = (/x:=s/ t1) ; (/x:=s/ t2)}>
  | <{if t1 then t2 else t3}> =>
        <{if (/x:=s/ t1) then (/x:=s/ t2) else (/x:=s/ t3)}>
  | exp_nvalue nv =>
    (fix w_rec (w : nvalue) : nvalue := 
    match w with
      | default l => default (l_s l)
      | device n l wl => device n (l_s l) (w_rec wl)
    end) nv
  | exp_literal l =>
      l_s l
  end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).
*)

(*Recursive on nvalues*)
Fixpoint bounded (e:exp) (l_bounded:list string) {struct e}: Prop :=
let l_b := 
  (fix l_b (l : literal) : Prop := 
        match l with
        | l_uid =>
          True
        | l_self e0 => 
           bounded e0 nil
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
        | l_mult t1 t2 =>
          (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
        | l_nvalue_get t1 t2 =>
            (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
        | l_nvalue_getDefault t1 =>
        (bounded t1 l_bounded)
        | <{fun n [y:T] {t1}}> =>
            bounded t1 (cons y l_bounded)
        | l_nfold e0 e1 e2 => 
            (bounded e0 nil) /\ (bounded e1 nil) /\ (bounded e2 nil) 
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
  | <{if t1 then t2 else t3}> =>
    (bounded t1 l_bounded) /\ (bounded t2 l_bounded)
    /\ (bounded t3 l_bounded)
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





