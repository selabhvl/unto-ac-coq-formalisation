From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.


Inductive event := e : nat -> nat -> event.

Definition E_net := list event.

Definition equalsEv (e0:event) (e1:event) := 
match (e0,e1) with (e id0 n0,e id1 n1) => (id0 =? id1) && (n0 =? n1) end.

Inductive relation := forward : event -> event -> relation.

Definition equalsR (r0:relation) (r1:relation) := match (r0,r1) with 
| (forward e0_in e0_out,forward e1_in e1_out) => if ((equalsEv e0_in e1_in) && (equalsEv e0_out e1_out)) then true else false end.

Definition R_net := list relation.

Fixpoint containsR (rel:relation) (rl:R_net) : bool :=
match rl with 
|cons r_el next => if (equalsR r_el rel) then true else (containsR rel next)
|nil => false 
end. 

Definition d_net := event -> ident.
Definition base_d (e:event) := 0.
Definition add_d (new_e:event) (new_d:ident) (old:d_net): d_net :=(fun e => if (equalsEv e new_e) then new_d else (old e)).

Definition s_net := event -> sensor_state.
Definition base_s (e:event) := base.
Definition add_s (new_e:event) (new_s:sensor_state) (old:s_net): s_net :=(fun e => if (equalsEv e new_e) then new_s else (old e)).


Inductive AES := aes : E_net -> R_net -> d_net -> s_net -> AES.

(*Need to check if nvalue is homogeneus in semantics*)
Definition STV := event -> nvalue.
Definition base_STV (e:event) := default l_fail.
Definition add_STV (new_e:event) (new_w:nvalue) (old:STV): STV := (fun e => if (equalsEv e new_e) then new_w else (old e)).

Definition vt_net := event -> value_tree.
Definition base_vt (e:event) := empty nil.
Definition add_vt (new_e:event) (new_vt:value_tree) (old:vt_net): vt_net :=(fun e => if (equalsEv e new_e) then new_vt else (old e)).


Fixpoint before_event (b_e:event) (b_E:E_net) (b_R:R_net) (b_vts:vt_net) (b_d:d_net): value_tree_env :=
match b_E with 
| cons e_el next => if (containsR (forward e_el b_e) b_R) then vt_el (b_d e_el) (b_vts e_el) (before_event b_e next b_R b_vts b_d) 
else (before_event b_e next b_R b_vts b_d)
| nil => vt_end
end.

Definition ex_E: E_net := cons (e 0 0) (cons (e 0 1) (cons (e 1 0) (cons (e 1 1) (cons (e 3 0) nil)))).

Definition ex_R: R_net := cons (forward (e 3 0) (e 0 1)) (cons (forward (e 1 1) (e 0 1)) nil).

Definition ex_vts := add_vt (e 1 1) (some <{[0>>3][>5]}> nil) (add_vt (e 3 0) (some <{[0>>5][>5]}> nil) base_vt).

Definition ex_d := add_d (e 0 0) 0 (add_d (e 0 1) 0 (add_d (e 1 0) 1 (add_d (e 1 1) 1 (add_d (e 3 0) 3 (base_d))))).

Compute (before_event (e 0 1) ex_E ex_R ex_vts ex_d).















