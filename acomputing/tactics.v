From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.


(*It's beter to replace auto with apropriate basic tactic*)
Ltac ordered_tac := solve [apply ordered0 | apply ordered1 | apply ordered2;auto;ordered_tac].
Ltac w_tac := solve [split; [>ordered_tac | simpl;auto]].

Ltac nval_tac := solve [apply E_NVAL; w_tac].

Ltac lit_tac := solve [apply E_LIT; unfold value; simpl; auto].

Ltac var_tac := 
apply E_VAR;
[>w_tac|
unfold base; repeat (unfold add); simpl;
lazymatch goal with 
| [|- context [l_fail]]=> fail
| _ => reflexivity
end].

Ltac mult_tac  := 
solve [apply A_MULT;
match goal with
| [|- w_value ?X] => w_tac
| _ => nval_tac
end].

Ltac fun_tac := apply A_FUN; [>w_tac|w_tac|simpl].

Ltac sens_tac := 
apply A_SENS;
[>w_tac|
unfold base; repeat (unfold add); simpl;
lazymatch goal with 
| [|- context [l_fail]]=> fail
| _ => reflexivity
end].

Ltac self_tac := apply A_SELF; [>w_tac|reflexivity].

Ltac uid_tac := apply A_UID.

Ltac app_tac x y:= apply E_APP with (w0:=x) (w1:=y); [>w_tac|w_tac|w_tac|simpl;auto|apply func|idtac "TO SOLVE E1"|idtac "TO SOLVE E2"|idtac "TO SOLVE FUN"].

Ltac nfold_tac := eapply A_FOLD;[>w_tac|w_tac|w_tac|unfold value;simpl;auto|simpl].


Definition x:string := "x".
Definition y:string := "y".
Definition z:string := "z".
Definition s0:string := "s0".
Definition s1:string := "s1".
Definition fun0:string := "fun0".

Lemma mult: <[ 10 | base | vt_end |   <{mult ([1>>5][2>>5][>5]) ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
mult_tac.
Qed.

Lemma wrong_mult: <[ 10 | base | vt_end |   <{mult ([2>>5][2>>5][>5]) ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
try mult_tac.
Abort.

Lemma lit: <[ 10 | base | vt_end |   <{ 5 }> ]> ==> <[ <{[>5]}> | empty nil ]>.
Proof.
lit_tac.
Qed.

Lemma wrong_lit: <[ 10 | base | vt_end |   <{ fun fun0[x:Nat]{mult x y} }> ]> ==> <[ <{[>fun fun0[x:Nat]{mult x y}]}> | empty nil ]>.
Proof.
try lit_tac.
Abort.

Lemma var: <[10 | add y <{[>5]}> (add x <{[>6]}> base) | vt_end | <{y}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
var_tac.
Qed.

Lemma wrong_var: <[10 | add y <{[>5]}> (add y <{[>6]}> base) | vt_end | <{z}> ]> ==> <[ <{[>FAIL]}> | empty nil  ]>.
Proof.
try var_tac.
Abort.

Lemma func: <[10 | base | vt_end | <{fun fun0[x:Nat]{mult x ([>5])} ([>6])}> ]> ==> <[ <{[>30]}> | empty nil  ]>.
Proof.
fun_tac. mult_tac.
Qed.

Lemma wrong_func: <[10 | base | vt_end | <{fun fun0[x:Nat]{mult x ([>5])} ([>6])}> ]> ==> <[ <{[>25]}> | empty nil  ]>.
Proof.
try (fun_tac; mult_tac).
Abort.

Lemma sens: <[10 | add s0 <{[>5]}> (add s1 <{[>6]}> base) | vt_end | <{sensor s0}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
sens_tac.
Qed.

Lemma wrong_sens: <[10 | add s0 <{[>5]}> (add s1 <{[>6]}> base) | vt_end | <{sensor z}> ]> ==> <[ <{[>FAIL]}> | empty nil  ]>.
Proof.
try sens_tac.
Abort.

Lemma self: <[10 | base | vt_end | <{self ([10>>5][>6])}> ]> ==> <[ <{5}> | empty nil  ]>.
Proof.
self_tac.
Qed.

Lemma wrong_self: <[10 | base | vt_end | <{self ([10>>5][>6])}> ]> ==> <[ <{6}> | empty nil  ]>.
Proof.
try self_tac.
Abort.

Lemma uid: <[10 | base | vt_end | <{uid}> ]> ==> <[ <{10}> | empty nil  ]>.
Proof.
uid_tac.
Qed.

Lemma wrong_uid: <[10 | base | vt_end | <{uid}> ]> ==> <[ <{100}> | empty nil  ]>.
Proof.
try uid_tac.
Abort.

Lemma fold: <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{ nfold ([> fun fun0[x:Nat] {fun fun0[y:Nat] {mult x y} }]) ([2>>4][3>>5][>6]) ([>7]) }> ]> ==> <[ <{[>140]}> | empty nil ]>.
Proof.
nfold_tac.
app_tac <{[> fun fun0 [y : Nat] {mult ([>5]) y}]}> <{[>28]}>.
  -app_tac <{[ > fun fun0 [x : Nat] {fun fun0 [y : Nat] {mult x y}}]}> <{[>5]}>.
    +nval_tac.
    +lit_tac.
    +fun_tac. lit_tac.
  -app_tac <{[ > fun fun0 [y : Nat] {mult ([>4]) y}]}> <{[>7]}>.
    +app_tac <{[ > fun fun0 [x : Nat] {fun fun0 [y : Nat] {mult x y}}]}> <{[>4]}>. 
      nval_tac.
      lit_tac.
      fun_tac;lit_tac.
    +lit_tac.
    +fun_tac. mult_tac.
  -fun_tac. mult_tac.
Qed.

