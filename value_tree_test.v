
Require Import String. 
Require Import nvalue. 
Require Import value_tree.
Require Import Bool.

Check (some nat (default nat 5) (cons (some bool (default bool true) nill) nill)).

(*Returns first value tree in the list*)
Compute (pi 0 (empty (cons (some bool (default bool true) nill) (cons (some bool (default bool false) nill) 
(cons (some nat (default nat 5) nill) nill))))).

(*Returns second value tree in the list*)
Compute (pi 1 (empty (cons (some bool (default bool true) nill) (cons (some bool (default bool false) nill) 
(cons (some nat (default nat 5) nill) nill))))).

(*Returns third value tree in the list*)
Compute (pi 2 (empty (cons (some bool (default bool true) nill) (cons (some bool (default bool false) nill) 
(cons (some nat (default nat 5) nill) nill))))).

(*Returns empty value tree*)
Compute (pi 3 (empty (cons (some bool (default bool true) nill) (cons (some bool (default bool false) nill) 
(cons (some nat (default nat 5) nill) nill))))).


Definition vt_0: value_tree := empty (cons (some bool (default bool true) nill) (cons (some bool (default bool false) nill) 
(cons (some nat (default nat 5) nill) nill))).

Definition vt_1: value_tree := empty (cons (some bool (default bool false) nill) (cons (some bool (default bool true) nill) 
(cons (some nat (default nat 6) nill) nill))).

(*VALUE-TREE ENV*)

Check 
(
vt_el 0 ( vt_0 ) (
vt_el 1 ( vt_1)
(vt_end) 
)
).

Definition vt_env_0: value_tree_env :=  vt_el 0 ( vt_0 ) ( vt_el 1 ( vt_1) (vt_end)).

Compute (pi_env 0 vt_env_0).

Compute (pi_env 1 vt_env_0).

Compute (pi_env 2 vt_env_0).

Compute (pi_env 3 vt_env_0).

