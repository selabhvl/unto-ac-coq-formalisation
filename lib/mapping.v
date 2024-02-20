Require Import Maps.
Require Import BinNums.
From Coq Require Import String.
Require Import Ascii.
Require Import BinPosDef.
(*
Mapping interface
*)

Module Type KEY_TYPE.
  Declare Module IT : INDEXED_TYPE.

  Parameter t : Type.
  (* enable Mappings to cast values of t to the wrapped IT.t *)
  Parameter into : t -> IT.t.
End KEY_TYPE.

Module Type MAPPING (K : KEY_TYPE).
  
  Module M := IMap(K.IT).
  Module Key := K.IT.

  Parameter lookup : forall A : Type, K.t -> M.t A -> A.
  Parameter place : forall A : Type, K.t -> A -> M.t A -> M.t A.
  Definition MapOf (A : Type) := M.t A.
  Definition NewMap {A : Type} (def : A) := M.init def.

  Parameter fetch : forall A k v (m: M.t A), lookup A k (place A k v m) = v.

  (* Software fundations notations *)
  Notation "'_' '!->' v" := (NewMap _ v) (at level 100, right associativity).
  Notation "k '!->' v ';' m" := (place _ k v m) (at level 100, v at next level, right associativity).
  Notation "m '<-!' k" := (lookup _ k m) (at level 100, right associativity).
End MAPPING.


(*
  Implemented modules
*)

Module Mapping (K: KEY_TYPE) <: MAPPING(K).
  Module M := IMap(K.IT).
  Module Key := K.IT.

  Definition lookup {A : Type} (k : K.t) (map : M.t A) := M.get (K.into k) map.
  Definition place {A : Type} (k : K.t) (v : A) (map : M.t A) := M.set (K.into k) v map.
  Definition MapOf (A : Type) := M.t A.
  Definition NewMap {A : Type} (def : A) := M.init def.

  Lemma fetch : forall A k v (m: M.t A), lookup k (place k v m) = v.
  Proof. intros. apply M.gss. Qed.
End Mapping.


Module StringKey <: KEY_TYPE.
  Definition t := string.
  Definition into (x : t) : string := x.
  
  Module IT <: INDEXED_TYPE.
    Definition t := t.

    Local Definition bool_cons_pos (b : bool) (p : positive) : positive :=
      if b then p~1 else p~0.
    Local Definition ascii_cons_pos (c : ascii) (p : positive) : positive :=
      match c with
      | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
        bool_cons_pos b0 ( bool_cons_pos b1 ( bool_cons_pos b2 (
          bool_cons_pos b3 ( bool_cons_pos b4 ( bool_cons_pos b5 (
          bool_cons_pos b6 ( bool_cons_pos b7 p)))))))
      end.
    Fixpoint string_to_pos (s : string) : positive :=
      match s with
      | EmptyString => 1
      | String c s => ascii_cons_pos c (string_to_pos s)
      end.

    Definition index: t -> positive := string_to_pos.

    Theorem index_inj: forall (x y: t), index x = index y -> x = y.
    Proof. Admitted. (* TODO proof this *)

    Parameter eq: forall (x y: t), {x = y} + {x <> y}.

  End IT.

End StringKey.