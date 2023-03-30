
Require Import String.

Inductive sensor_state (A:Type): Type := 
| s_state_el (n:string) (v:A) : sensor_state A -> sensor_state A
| s_state_end : sensor_state A.

(*
Fixpoint charge_sensor_state (s:sensor_state A) (e:A) : A :=
match s with
| s_state_el n v l=> charge_sensor_state l (<{/n := v/ e}>)
| s_state_end => e
end. 
*)

