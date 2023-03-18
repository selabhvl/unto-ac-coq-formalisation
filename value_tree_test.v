
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