From AC Require Import syntax.
Require Import String.
Require Import Bool.

Definition sensor_state := string -> nvalue.

Definition getSens (n:string) (s:sensor_state) : nvalue := s n.


Definition base (s:string) := default l_fail.

Definition contains (s:string) (old:string->nvalue): bool :=
match (old s) with 
| default l_fail => false
| _ => true
end.

Definition add (s:string) (v:nvalue) (old:string->nvalue): (string->nvalue) :=(fun x => if String.eqb x s then v else (old x)).
