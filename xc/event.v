From AC Require Import syntax.
Require Import mapping.
Require Import Maps.
Require Import BinPosDef.

(*Inductive definition of type event*)
Inductive event := e : ident -> nat -> event.

(*A list of events*)
Definition E_net := list event.

Module EventKey <: KEY_TYPE.
  Definition t := event.
  Definition into (x : t) : event := x.
  
  Module IT <: INDEXED_TYPE.
    Definition t := t.

    Definition index (ev: t) : positive := 
      match ev with 
      | e i n => Pos.of_nat (i * n) (* This actually doesn't work because event 1 -> 53 != 53 -> 1*)
      end.

    Theorem index_inj: forall (x y: t), index x = index y -> x = y.
    Proof. Admitted. (* TODO proof this *)

    Parameter eq: forall (x y: t), {x = y} + {x <> y}.

  End IT.

End EventKey.