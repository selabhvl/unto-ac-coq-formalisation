Require Import expression.
Require Import String.

Inductive sensor_state: Type := 
| s_state_el (n:string) (v:exp) : sensor_state -> sensor_state
| s_state_end : sensor_state.

Fixpoint charge_sensor_state (s:sensor_state) (e:exp) : exp :=
match s with
| s_state_el n v l=> charge_sensor_state l (<{/n := v/ e}>)
| s_state_end => e
end. 

