From AC Require Import syntax.
Require Import String.
Require Import Bool.

Definition sensor_state := string -> nvalue.

Definition base_sens (s:string) := default l_fail.

Definition add_sens (s:string) (v:nvalue) (old:string->nvalue): (string->nvalue) :=(fun x => if String.eqb x s then v else (old x)).