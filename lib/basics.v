Require Import String.
Require Import Bool.
Require Import List.
From AC Require Import syntax.
From AC Require Import nvalues.

(* Substitution operations:
Takes in input the variable to replace, the value replaced and the involved expression 
Returns the resulting expression with all the unbounded variables replaced *)
Reserved Notation "'/' x ':=' s '/' t" (in custom acnotation at level 20, x constr).
Fixpoint subst (x : string) (s : exp) (t : exp) : exp :=
  match t with
  | exp_var y =>
      if String.eqb x y then s else t
  | <{fun n [y] {t1}}> =>
      if ((String.eqb x y) || (String.eqb x n)) then t else <{fun n [y] {/x:=s/ t1}}>
  | <{app t1 $ t2 $ }> =>
      <{app (/x:=s/ t1) $ (/x:=s/ t2) $}>
  | <{app t1 $ t2 t3 $ }> =>
      <{app (/x:=s/ t1) $ (/x:=s/ t2) (/x:=s/ t3) $}>
  | <{app t1 $ t2 t3 t4$ }> =>
      <{app (/x:=s/ t1) $ (/x:=s/ t2) (/x:=s/ t3) (/x:=s/ t4)$}>
  | <{val n = t1 ; t2}> =>
      if (String.eqb x n) then t else <{val n = (/x:=s/ t1) (*Dentro n non si può sostituire ?*) ; (/x:=s/ t2)}>
  | l_builtin b => l_builtin b
  | l_sensor s => l_sensor s
  | l_true => l_true
  | l_false => l_false
  | l_const n => l_const n
  | l_fail => l_fail
  | exp_nvalue w => <{w}>
end
where "'/' x ':=' s '/' t" := (subst x s t) (in custom acnotation).


(* Check if an expression is bounded and doesn't contains FAIL, 
Takes in input the expression to check and a list of variable that are already bounded
Return a proposition that can proved
The expression isn't well formed if contains a FAIL*)
Fixpoint well_formed (e:exp) (l_bounded:list string) {struct e}: Prop :=
let l_b := 
  (fix l_b (l : literal) : Prop := 
        match l with
        | l_builtin b => True
        | <{fun n [y] {t1}}> => 
              well_formed t1 (cons y l_bounded)
        | l_sensor s => True
        | l_fail => False (*A expression with fail is not well formed*)
        | l_true => True
        | l_false => True
        | l_const n => True
        end
    )
in
match e with 
  | exp_var y =>
    In y l_bounded
  | <{app t1 $ t2 $}> =>
    (well_formed t1 l_bounded) /\ (well_formed t2 l_bounded)
  | <{app t1 $ t2 t3 $}> =>
    (well_formed t1 l_bounded) /\ (well_formed t2 l_bounded) /\ (well_formed t3 l_bounded)
  | <{app t1 $ t2 t3 t4 $}> =>
    (well_formed t1 l_bounded) /\ (well_formed t2 l_bounded) /\ (well_formed t3 l_bounded) /\ (well_formed t4 l_bounded)
  | <{val n = t1 ; t2}> =>
    (well_formed t1 l_bounded) /\ (well_formed t2 (cons n l_bounded))
  | <{fun n [y] {t1}}> =>
    well_formed t1 (cons y l_bounded)
  | exp_nvalue w =>
    (fix w_rec (w : nvalue ) : Prop := 
    match w with
      | default l => l_b l
      | device _ l wl => l_b l /\ w_rec wl
    end) w
  | exp_literal l => l_b l
end.

(*A value is a well formed literal*)
Definition value (l:literal) : Prop := well_formed (exp_literal l) nil.

(*A nvalue is well formed if it's ordered contains valid values*)
Definition w_value (w:nvalue):= ordered w /\ well_formed w nil.

(*Proposition that check if a expression is a function*)
Inductive is_fun: exp -> Prop :=
  | func : forall n x t1, 
      is_fun <{fun n [x] {t1}}>
  | built : forall b, 
      is_fun (exp_literal (l_builtin b)).









