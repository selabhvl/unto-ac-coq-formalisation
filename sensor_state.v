Require Import String.

Inductive sensor_state: Type := 
| s_state_el (A:Type) (s:string) (v:A) : sensor_state -> sensor_state
| s_state_end : sensor_state.

