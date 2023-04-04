From AC Require Import sensor_state.
From AC Require Import syntax.
Require Import String.

Compute (getSens "x"%string (fun (x:string) => (if String.eqb "x" x then (default 5) else (default 8))) ).

Compute (getSens "m" (add "m" (default <{true}>) (add "x" (default 5) (base))) ).