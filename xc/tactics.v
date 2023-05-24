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

Definition x:string := "x".
Definition y:string := "y".
Definition z:string := "z".
Definition s0:string := "s0".
Definition s1:string := "s1".
Definition fun0:string := "fun0".

(*It's beter to replace auto with apropriate basic tactic*)
Ltac ordered_tac := solve [apply ordered0 | apply ordered1 | apply ordered2;auto;ordered_tac].
Ltac w_tac := solve [split; [>ordered_tac | simpl;repeat split;auto]].

Ltac nval_tac := solve [eapply E_NVAL; w_tac].

Ltac lit_tac := solve [eapply E_LIT; unfold value; simpl; repeat split; auto].

Ltac var_tac := 
eapply E_VAR;
unfold base; repeat (unfold add); simpl;
[(lazymatch goal with 
| [|- context [l_fail]]=> fail;idtac "No sensor"
| _ => reflexivity;w_tac
end)|w_tac].

Ltac mult_tac  := 
solve [eapply A_MULT;
match goal with
| [|- context [l_fail] ] => fail
| [|- w_value ?X] => try w_tac
| _ => nval_tac
end].

Ltac or_tac  := 
solve [eapply A_OR;
match goal with
| [|- context [l_fail] ] => fail
| [|- w_value ?X] => try w_tac
| _ => nval_tac
end].

Ltac and_tac := 
solve [eapply A_AND;
match goal with
| [|- context [l_fail] ] => fail
| [|- w_value ?X] => try w_tac
| _ => nval_tac
end].

Ltac fun_tac := eapply A_FUN; [>w_tac|simpl| try w_tac].

Ltac sens_tac := 
eapply A_SENS;
unfold base; repeat (unfold add); simpl;
[(lazymatch goal with 
| [|- context [l_fail]]=> fail;idtac "No sensor"
| _ => reflexivity;w_tac
end)|w_tac].

Ltac self_tac := eapply A_SELF; [>w_tac|reflexivity].

Ltac uid_tac := eapply A_UID.

Ltac app_tac x y:= apply E_APP with (w0:=x) (w1:=y); [>idtac "TO SOLVE E1"|w_tac|simpl;auto|apply func|idtac "TO SOLVE E2"|w_tac|idtac "TO SOLVE FUN"|w_tac].

Ltac nfold_tac := eapply A_FOLD;[>w_tac|w_tac|w_tac|simpl|unfold value;simpl;auto].

Ltac exchange_tac := eapply A_EXCHANGE; [w_tac|w_tac|simpl|try w_tac].

(*Importante mettere i builtin prima altrimenti li prende come applicazioni*)
Ltac device_tac :=
repeat (
first [
simpl;auto;
(match goal with 
| [|- w_value ?X] =>idtac "W_TAC"; w_tac
| [|- value ?X] => idtac "VALUE";unfold value; simpl; repeat split; auto
| [|- is_fun ?X] => idtac "FUNC"; apply func + apply built
| _ => fail
end
)
| eapply A_MULT;idtac "MULT"

| eapply A_UID;idtac "UID"
| eapply A_FOLD;idtac "FOLD"
| eapply A_SELF;idtac "SELF"
| eapply A_EXCHANGE;idtac "EXCHANGE"
| eapply A_OR;idtac "OR"
| eapply A_AND;idtac "OR"

| eapply E_NVAL;idtac "NVAL"
| eapply A_SENS;idtac "SENS"
| eapply E_LIT;idtac "LIT"
| eapply E_VAR;idtac "VAR"

| eapply A_FUN;idtac "FUN"

| eapply E_APP_3;idtac "APP_3"
| eapply E_APP_2;idtac "APP_2"
| eapply E_APP;idtac "APP"



| eapply A_SELF;idtac "SELF"

]).




Lemma mult: exists (w:nvalue), <[ 10 | base | vt_end |   <{app mult $ ([1>>5][2>>5][>5]) ([1>>5][>6]) $ }> ]> ==> <[ <{ w}> | empty nil ]>.
Proof. eexists.
mult_tac.
Qed.

Lemma wrong_mult: exists (w:nvalue), <[ 10 | base | vt_end |   <{app mult $ ([1>>5][2>>5][>5]) ([1>>5][>6]) $ }> ]> ==> <[ <{ w }> | empty nil ]>.
Proof.
eexists. mult_tac.
Abort.

Lemma lit: <[ 10 | base | vt_end |   <{ 5 }> ]> ==> <[ <{[>5]}> | empty nil ]>.
Proof.
lit_tac.
Qed.

Lemma wrong_lit: <[ 10 | base | vt_end |   <{ fun fun0[x]{app mult $x y$} }> ]> ==> <[ <{[>fun fun0[x]{app mult $x y$}]}> | empty nil ]>.
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

Lemma p_func: <[10 | base | vt_end | <{app  (fun fun0[x]{app mult $x ([>5])$}) $([>6])$}> ]> ==> <[ <{[>30]}> | empty nil  ]>.
Proof.
fun_tac. mult_tac.
Qed.

Lemma wrong_p_func: <[10 | base | vt_end | <{app fun fun0[x]{app mult $x ([>5])$} $([>6])$}> ]> ==> <[ <{[>25]}> | empty nil  ]>.
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

Lemma self: <[10 | base | vt_end | <{app self $([10>>5][>6])$}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
self_tac.
Qed.

Lemma wrong_self: <[10 | base | vt_end | <{app self $([10>>5][>6])$}> ]> ==> <[ <{6}> | empty nil  ]>.
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

Lemma fold: <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $([> fun fun0[x] {fun fun0[y] {app mult $x y$} }]) ([2>>3][3>>5][>6]) ([>7])$ }> ]> ==> <[ <{[>105]}> | empty nil ]>.
Proof.
device_tac.
Qed.

Lemma fold_or: <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $[>(fun fun0[x] {fun fun0[y] {app b_or $x y$} })] ([2>>true][3>>false][>6]) [>false]$ }> ]> ==> <[ <{[>true]}> | empty nil ]>.
Proof.
device_tac.
Qed.

Lemma e_fold_or: exists (w:nvalue) (vt:value_tree), <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $[>(fun fun0[x] {fun fun0[y] {app b_or $x y$} })] ([2>>true][3>>false][>6]) [>false]$ }> ]> ==> <[ <{w}> | vt ]>.
Proof. eexists. eexists.
device_tac.
Qed.


Lemma p_exchange : <[ 10 | base | vt_el 2 (some <{[10>>4][>6]}> nil) (vt_el 3 (some <{[10>>6][>6]}> nil) (vt_end)) | <{app exchange $([>5]) ([>fun fun0[x]{x}])$}> ]>  ==> 
<[ <{[2>>4][3>>6][>5]}> | some <{[2>>4][3>>6][>5]}> (cons (some <{[>fun fun0[x]{x}]}> (cons (empty nil) (cons (empty nil) (cons (empty nil) nil))) ) nil) ]>. 
Proof. 
exchange_tac. simpl. eapply E_APP.
-nval_tac.
-w_tac.
-auto.
-apply func.
-nval_tac.
-w_tac.
-simpl. fun_tac. nval_tac.
-w_tac.
Qed.

Lemma e_fold: <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $([> fun fun0[x] {fun fun0[y] {app mult $x y$} }]) ([2>>4][3>>5][>6]) ([>7]) $}> ]> ==> <[ <{[>140]}> | empty nil ]>.
Proof.
device_tac.
Qed.





