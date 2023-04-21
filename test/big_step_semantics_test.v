From AC Require Import syntax.
From AC Require Import big_step_semantics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import basics.
From AC Require Import nvalues.
Require Import String.

(*NOTATION*)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition n : string := "n".
Definition fun0: string := "fun0". 
Definition fun1: string := "fun1". 

Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Lemma multiplication: <[ 10 | base | vt_end |   <{([2>>5][>5]) * ([1>>5][>6]) }> ]> ==> <[ <{ [1>>25][2>>30][>30]}> | empty nil ]>.
Proof.
apply A_MULT.
-split. apply ordered1. apply w_device. apply v_nat. apply w_default. apply v_nat.
-split. apply ordered1. apply w_device. apply v_nat. apply w_default. apply v_nat.
-split. apply ordered2. auto. apply ordered1. apply w_device. apply v_nat. apply w_device. apply v_nat. apply w_default. apply v_nat.
-simpl. apply E_NVAL. 
split. apply ordered2. auto. apply ordered1. apply w_device. apply v_nat. apply w_device. apply v_nat. apply w_default. apply v_nat.
Qed.

Lemma fold00: <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{ nfold [> fun fun0[x:Nat] {fun fun0[y:Nat] {x*y} }] [2>>4][3>>5][>6] [>7] }> ]> ==> <[ <{[>140]}> | empty nil ]>.
Proof.
eapply A_FOLD.
-split. 
+ apply ordered0.
+ apply w_default. apply v_abs. simpl. split. right. left. reflexivity. left. reflexivity.
-split. 
+apply ordered2. auto. apply ordered1.
+ apply w_device. apply v_nat. apply w_device. apply v_nat. apply w_default. apply v_nat.
-split. 
+ apply ordered0.
+ apply w_default. apply v_nat.
- apply v_nat.
- simpl. apply E_APP with (w0:=<{[> fun fun0 [y : Nat] { [>5] * y}]}>) (w1:=<{[>28]}>).
+ split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
+ split. apply ordered0. apply w_default. apply v_nat.
+ split. apply ordered0. apply w_default. apply v_nat.
+ simpl. auto. 
+ apply func.

+ apply E_APP with (w0:=<{[ > fun fun0 [x : Nat] {fun fun0 [y : Nat] {x * y}}]}>) (w1:=<{[>5]}>).
split. apply ordered0. apply w_default. apply v_abs. simpl. split. right. left. reflexivity. left. reflexivity.
split. apply ordered0. apply w_default. apply v_nat. 
split. apply ordered0. apply w_default. apply v_abs. simpl. auto. 
simpl. auto. apply func. 
apply E_NVAL.
split. apply ordered0. apply w_default. apply v_abs. simpl. split. right. left. reflexivity. left. reflexivity.
apply E_LIT. apply v_nat. 
apply A_FUN. split. apply ordered0. apply w_default. apply v_nat. split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
simpl. apply E_LIT.  apply v_abs. simpl. auto.

+ apply E_APP with (w0:=<{[ > fun fun0 [y : Nat] {[>4] * y}]}>) (w1:=<{[>7]}>).
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. auto. apply func. 
apply E_APP with (w0:=<{[ > fun fun0 [x : Nat] {fun fun0 [y : Nat] {x * y}}]}>) (w1:=<{[>4]}>).
split. apply ordered0. apply w_default. apply v_abs. simpl. split. right. left. reflexivity. left. reflexivity.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
simpl. auto. apply func. apply E_NVAL. 
split. apply ordered0. apply w_default. apply v_abs. simpl. split. right. left. reflexivity. left. reflexivity.
apply E_LIT. apply v_nat. apply A_FUN. split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto. simpl. 
apply E_LIT. apply v_abs. simpl. auto. 
apply E_LIT. apply v_nat.
apply A_FUN. split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. apply A_MULT. 
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. apply E_NVAL. split. apply ordered0. apply w_default. apply v_nat.

+apply A_FUN. split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. apply A_MULT.  
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. apply E_NVAL. split. apply ordered0. apply w_default. apply v_nat.

Qed.


Lemma fold00_R: <[ 4 | base | vt_el 2 (empty nil) (vt_el 3 (empty nil) (vt_end)) | <{ nfold [> fun fun0[x:Nat] {fun fun0[y:Nat] {x*y} }] [2>>4][3>>5][>6] [>7] }> ]> ==> <[ <{[>140]}> | empty nil ]>.
Proof. 
(*C0 call*)
eapply A_FOLD_R with (l0:=<{28}>).
(*C0: Preconditions*) 
auto. split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered2. auto. apply ordered1. apply w_device. apply v_nat. apply w_device. apply v_nat. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
apply v_nat.
apply v_nat.
(*C0: Exteternal application E_APP0*)
simpl. apply E_APP with (w0:=<{[>fun fun0 [y : Nat] {[>4] * y}]}>) (w1:=<{[>7]}>).
(*C0: E_APP0:  Preconditions*)
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. auto. apply func.
(*C0: E_APP0: Internal application I_APP0 e1 ==> w1*)
apply E_APP with (w0:=<{[> fun fun0[x:Nat] {fun fun0[y:Nat] {x*y} }]}>) (w1:=<{[>4]}>).
(*C0: E_APP0: I_APP0 Preconditions*)
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
simpl. auto. apply func. 
(*C0: E_APP0: I_APP0 e0 ==> w0*)
apply E_NVAL. split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
(*C0: E_APP0: I_APP0 e1 ==> w1*)
apply E_LIT. apply v_nat.
(*C0: E_APP0: I_APP0 function f w1 => w2*)
apply A_FUN. 
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
simpl. apply E_LIT. apply v_abs. simpl. auto.
(*C0: E_APP0: e1 ==> w1*)
apply E_NVAL. split. apply ordered0. apply w_default. apply v_nat.
(*C0: E_APP0: I_APP0 function f w1 ==> w2*)
apply A_FUN. 
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. 
apply A_MULT. 
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. apply E_NVAL. split. apply ordered0. apply w_default. apply v_nat.
(*C0: Recursive call C1*)
eapply A_FOLD_B.
(*C0:C1: Preconditions*)
auto.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered2. auto. apply ordered1. apply w_device. apply v_nat. apply w_device. apply v_nat.
  apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat. 
apply v_nat.
(*C0: C1: External application E_APP01*)
simpl. eapply E_APP with (w0:=<{[>fun fun0 [y : Nat] {[>5] * y}]}>) (w1:=<{[>28]}>).
(*C0: C1: E_APP01: Preconditions*)
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. auto. apply func.
(*C0: C1: E_APP01: Internal application I_APP01 e0==>w0*)
eapply E_APP with (w0:=<{[>fun fun0[x:Nat] {fun fun0[y:Nat] {x*y} }]}>) (w1:=<{[>5]}>).
(*C0: C1: E_APP01: I_APP01: Preconditions*)
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
simpl. auto. apply func.
(*C0: C1: E_APP01: I_APP01: e0 ==> w0*)
apply E_NVAL. split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
(*C0: C1: E_APP01: I_APP01: e1 ==> w1*)
apply E_LIT. apply v_nat.
(*C0: C1: E_APP01: I_APP01: function f w1 ==> w2*)
apply A_FUN. 
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_abs. simpl. auto.
simpl. apply E_LIT. apply v_abs. simpl. auto.
(*C0: C1: E_APP01: e1 ==> w1 *)
apply E_NVAL. split. apply ordered0. apply w_default. apply v_nat.
(*C0: C1: E_APP01: function f f w1 ==> w2 *)
apply A_FUN. split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. 
apply A_MULT. 
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
split. apply ordered0. apply w_default. apply v_nat.
simpl. apply E_NVAL.  split. apply ordered0. apply w_default. apply v_nat.

