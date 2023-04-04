
Require Import String. 
From AC Require Import syntax.
From AC Require Import nvalues. 
From AC Require Import value_tree.
Require Import Bool.

Check (some (default 5) (cons (some (default <{true}> ) nil) nil)).

(*Returns first value tree in the list*)
Compute (pi 0 (empty (cons (some (default <{true}> ) nil) (cons (some (default <{false}> ) nil) 
(cons (some (default 5) nil) nil))))).

(*Returns second value tree in the list*)
Compute (pi 1 (empty (cons (some (default <{true}>) nil) (cons (some (default <{false}>) nil) 
(cons (some (default 5) nil) nil))))).

(*Returns third value tree in the list*)
Compute (pi 2 (empty (cons (some (default <{true}>) nil) (cons (some (default <{false}>) nil) 
(cons (some (default 5) nil) nil))))).

(*Returns empty value tree*)
Compute (pi 3 (empty (cons (some (default <{true}>) nil) (cons (some (default <{false}>) nil) 
(cons (some (default 5) nil) nil))))).


Definition vt_0: value_tree := empty (cons (some (default <{true}>) nil) (cons (some (default <{false}>) nil) 
(cons (some (default 5) nil) nil))).

Definition vt_1: value_tree := empty (cons (some (default <{false}>) nil) (cons (some (default <{true}>) nil) 
(cons (some (default 6) nil) nil))).

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

