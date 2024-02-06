From AC Require Import syntax.
From AC Require Import basics.
(* From AC Require Import sensor_state. *)
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
From AC Require Import network_semantics.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.

Require Import Maps.
Require Import mapping.

Module Import NS := NetworkSemantics(Mapping).

Definition x:string := "x".
Definition y:string := "y".
Definition z:string := "z".
Definition s0:string := "s0".
Definition s1:string := "s1".
Definition fun0:string := "fun0".

(*Automaticaly check if nvalues is ordered*)
Ltac ordered_tac := solve [apply ordered0 | apply ordered1 | apply ordered2;auto;ordered_tac].

(*Automaticali check *)
Ltac w_tac := solve [split; [>ordered_tac | simpl;repeat split;auto]].

(*E-NVAL*)
Ltac nval_tac := solve [apply E_NVAL; w_tac].

(*E-NVAL*)
Ltac lit_tac := solve [apply E_LIT; unfold value; simpl; repeat split; auto].

Ltac var_tac := 
apply E_VAR;
unfold base_sens; repeat (unfold add_sens); simpl;
[(lazymatch goal with 
| [|- context [l_fail]]=> fail;idtac "No sensor"
| _ => reflexivity;w_tac
end)|w_tac].

Ltac mult_tac  := 
solve [apply A_MULT;
match goal with
| [|- context [l_fail] ] => fail
| [|- w_value ?X] => try w_tac
| _ => reflexivity
end].

Ltac or_tac  := 
solve [apply A_OR;
match goal with
| [|- context [l_fail] ] => fail
| [|- w_value ?X] => try w_tac
| _ => reflexivity
end].

Ltac and_tac := 
solve [apply A_AND;
match goal with
| [|- context [l_fail] ] => fail
| [|- w_value ?X] => try w_tac
| _ => reflexivity
end].

Ltac fun_tac := eapply A_FUN; [>w_tac|simpl| try w_tac].

Ltac sens_tac := 
eapply A_SENS;
unfold base_sens; repeat (unfold add_sens); simpl;
[(lazymatch goal with 
| [|- context [l_fail]]=> fail;idtac "No sensor"
| _ => reflexivity;w_tac
end)|w_tac].

Ltac self_tac := apply A_SELF; [>w_tac|reflexivity].

Ltac uid_tac := apply A_UID.

Ltac app_tac x y:= apply E_APP with (w0:=x) (w1:=y); [>idtac "TO SOLVE E1"|w_tac|simpl;auto|apply func|idtac "TO SOLVE E2"|w_tac|idtac "TO SOLVE FUN"|w_tac].

Ltac val_tac x := apply E_VAL with (w1:=x); [>idtac "TO SOLVE E1"|w_tac|idtac "TO SOLVE E2"|w_tac].

Ltac nfold_tac := eapply A_FOLD;[>w_tac|w_tac|w_tac|simpl|unfold value;simpl;auto].

Ltac exchange_tac := eapply A_EXCHANGE; [w_tac|w_tac|simpl|try w_tac].


Ltac device_tac :=
repeat (
first [
simpl;auto;
(match goal with 
| [|- w_value ?X] =>idtac "W_TAC"; w_tac
| [|- value ?X] => idtac "VALUE";unfold value; simpl; repeat split; auto
| [|- is_fun ?X] => idtac "FUNC"; apply func + apply built
| [|- bigstep (Input ?id ?s ?v_env (exp_nvalue ?w)) (Output (exp_nvalue ?w) (empty nil) )] => idtac "GOP"
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
| eapply E_VAL;idtac "VAL"

| eapply A_SELF;idtac "SELF"

]).

Ltac net_tac :=
repeat 
(match goal with 
| [|- net_val (netI (aes nil ?n_R ?n_d ?n_s) ?exp) (netO ?stv ?vts) ] => idtac "BASE";eapply E_NET_0 
| [|- ?Y = ?X] => idtac "ENV"; reflexivity
| [|- bigstep ?X ?Y] => idtac "DEVICE"; device_tac
| _ => idtac "REC";eapply E_NET_R 
end).

Lemma fdfsd: netI (aes (nil) nil base_d base_s) <{[>5]}> |=> netO nil nil.
Proof.
net_tac.
Qed.


Lemma val_ev: <[ 10 | base_sens | vt_end | <{val x=5 ; app mult $x [1>>2][>3]$ }> ]> ==> <[ <{[1>>10][>15]}> | empty (cons (empty nil) (cons (empty nil) nil))  ]>.
Proof.
val_tac (<{[>5]}>). lit_tac. simpl. mult_tac.
Qed.

Lemma mult:  <[ 10 | base_sens | vt_end |   <{app mult $ ([1>>5][2>>5][>5]) ([1>>5][>6]) $ }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
mult_tac.
Qed.

Lemma wrong_mult: exists (w:nvalue), <[ 10 | base_sens | vt_end |   <{app mult $ ([1>>5][2>>5][>5]) ([1>>5][>6]) $ }> ]> ==> <[ <{ w }> | empty nil ]>.
Proof.
eexists. mult_tac.
Qed.

Lemma lit: <[ 10 | base_sens | vt_end |   <{ 5 }> ]> ==> <[ <{[>5]}> | empty nil ]>.
Proof.
lit_tac.
Qed.

Lemma wrong_lit: <[ 10 | base_sens | vt_end |   <{ fun fun0[x]{app mult $x y$} }> ]> ==> <[ <{[>fun fun0[x]{app mult $x y$}]}> | empty nil ]>.
Proof.
try lit_tac.
Abort.

Lemma var: <[10 | add_sens y <{[>5]}> (add_sens x <{[>6]}> base_sens) | vt_end | <{y}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
var_tac.
Qed.

Lemma wrong_var: <[10 | add_sens y <{[>5]}> (add_sens y <{[>6]}> base_sens) | vt_end | <{z}> ]> ==> <[ <{[>FAIL]}> | empty nil  ]>.
Proof.
try var_tac.
Abort.


Lemma p_func:exists c, <[10 | base_sens | vt_end | <{app  (fun fun0[x]{app mult $x ([>FAIL])$}) $([>6])$}> ]> ==> <[ c | empty nil  ]>.
Proof. eexists.
device_tac.  
Abort.

Lemma wrong_p_func: <[10 | base_sens | vt_end | <{app fun fun0[x]{app mult $x ([>5])$} $([>6])$}> ]> ==> <[ <{[>25]}> | empty nil  ]>.
Proof.
try (fun_tac; mult_tac).
Abort.

Lemma sens: <[10 | add_sens s0 <{[>5]}> (add_sens s1 <{[>6]}> base_sens) | vt_end | <{sensor s0}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
sens_tac.
Qed.

Lemma wrong_sens: <[10 | add_sens s0 <{[>5]}> (add_sens s1 <{[>6]}> base_sens) | vt_end | <{sensor z}> ]> ==> <[ <{[>FAIL]}> | empty nil  ]>.
Proof.
try sens_tac.
Abort.

Lemma self: <[10 | base_sens | vt_end | <{app self $([10>>5][>6])$}> ]> ==> <[ <{[>5]}> | empty nil  ]>.
Proof.
self_tac.
Qed.

Lemma wrong_self: <[10 | base_sens | vt_end | <{app self $([10>>5][>6])$}> ]> ==> <[ <{[>6]}> | empty nil  ]>.
Proof.
try self_tac.
Abort.

Lemma uid: <[10 | base_sens | vt_end | <{uid}> ]> ==> <[ <{[>10]}> | empty nil  ]>.
Proof.
uid_tac.
Qed.

Lemma wrong_uid: <[10 | base_sens | vt_end | <{uid}> ]> ==> <[ <{[>100]}> | empty nil  ]>.
Proof.
try uid_tac.
Abort.

Lemma fold: <[ 4 | base_sens | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $([> fun fun0[x] {fun fun0[y] {app mult $x y$} }]) ([2>>3][3>>5][>6]) ([>7])$ }> ]> ==> <[ <{[>105]}> | empty nil ]>.
Proof.
device_tac.
Qed.

Lemma fold_or: <[ 4 | base_sens | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $[>(fun fun0[x] {fun fun0[y] {app b_or $x y$} })] ([2>>true][3>>false][>6]) [>false]$ }> ]> ==> <[ <{[>true]}> | empty nil ]>.
Proof.
device_tac.
Qed.

Lemma e_fold_or: exists (w:nvalue) (vt:value_tree), <[ 4 | base_sens | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $[>(fun fun0[x] {fun fun0[y] {app b_or $x y$} })] ([2>>true][3>>false][>6]) [>false]$ }> ]> ==> <[ <{w}> | vt ]>.
Proof. eexists. eexists.
device_tac.
Qed.


Lemma p_exchange : <[ 10 | base_sens | vt_el 2 (some <{[10>>4][>6]}> nil) (vt_el 3 (some <{[10>>6][>6]}> nil) (vt_end)) | <{app exchange $([>5]) ([>fun fun0[x]{x}])$}> ]>  ==> 
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

Lemma e_fold: <[ 4 | base_sens | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{app nfold $([> fun fun0[x] {fun fun0[y] {app mult $x y$} }]) ([2>>4][3>>5][>6]) ([>7]) $}> ]> ==> <[ <{[>140]}> | empty nil ]>.
Proof.
device_tac.
Qed.





