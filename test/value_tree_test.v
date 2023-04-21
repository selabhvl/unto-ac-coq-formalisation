
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

(*Test name_f*)
Definition pop:string:="pop".
Definition top:string:="top".
Definition x:string:="x".
Compute (name_f <{fun pop[x:Nat] {5} }>).
Compute (name_f <{x}>).

(*Test select_f*)

Compute (select_f  (vt_el 5 (some <{[>fun pop[x:Nat] {5}]}> nil ) 
(vt_el 6 (some <{[>fun pop[x:Nat] {5}]}> nil ) vt_end ) )  <{fun pop[x:Nat] {5} }>).

Compute (select_f  (vt_el 5 (some <{[>fun pop[x:Nat] {5}]}> nil ) 
(vt_el 6 (some <{[>fun top[x:Nat] {5}]}> nil ) vt_end ) )  <{fun pop[x:Nat] {5} }>).

Compute (select_f  (vt_el 5 (some <{[>fun pop[x:Nat] {5}]}> nil ) 
(vt_el 6 (some <{[>6]}> nil ) vt_end ) )  <{fun pop[x:Nat] {5} }>).

(*Test get_messages*)

Compute (get_messages 2 <{[>5]}> (vt_el 3 (some <{[2>>5][>6]}> nil) 
(vt_el 4 (some <{[1>>2][2>>6][>7]}> nil) (vt_el 7 (some <{[1>>2][2>>6][>7]}> nil) vt_end ) )  )).

Compute (get_messages 2 <{[>5]}> (vt_el 3 (some <{[2>>5][>6]}> nil) 
(vt_el 4 (some <{[1>>2][2>>6][>7]}> nil) (vt_el 7 (empty nil) vt_end ) )  )).


