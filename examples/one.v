From AC Require Import syntax.
From AC Require Import basics.
(* From AC Require Import sensor_state. *)
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
From AC Require Import network_semantics.
(* From AC Require Import tactics. *)
Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.


Definition fun_ex: string := "fun0". 
Definition fun_or_x: string := "fun_or_x". 
Definition fun_or_y: string := "fun_or_y". 
Definition f1: string := "f1". 
Definition f2: string := "f2". 
Definition old: string := "old". 

Require Import Maps.
Require Import mapping.
Module M := Mapping(StringKey).
Module Import NS := NetworkSemantics(Mapping).
(** Event list*)
Definition eventList: E_net := (e 0 2) :: (e 1 2) :: (e 2 2) :: (e 0 1) :: (e 1 1) :: (e 2 1) ::  (e 0 0) :: (e 1 0) :: (e 2 0) :: nil.

(** Relation list*)
Definition messageList: R_net := forward (e 0 0) (e 0 1) :: forward (e 0 0) (e 1 1) :: forward (e 1 0) (e 1 1) ::
forward (e 2 0) (e 1 1) :: forward (e 2 0) (e 2 1) :: forward (e 0 1) (e 0 2) :: forward (e 0 1) (e 2 2) ::
forward (e 1 1) (e 0 2) :: forward (e 1 1) (e 1 2) :: forward (e 1 1) (e 2 2) :: forward (e 2 1) (e 0 2) :: 
forward (e 2 1) (e 2 2) :: nil.

(** Device map*)
Definition deviceMap (e:event): nat :=  match e with | (e id n) => id end.

(** Sensors state of the net for each event*)
Definition sensorMap (ev:event): sensor_state :=
  match ev with 
  | e 1 0 => M.place f1 <{[>true]}> (M.place f2 <{[>false]}> (M.NewMap (default l_false)))(* add_sens f1 <{[>true]}> (add_sens f2 <{[>false]}> base_sens)*)
  | e 2 0 => M.place f1 <{[>false]}> (M.place f2 <{[>true]}> (M.NewMap (default l_false)))(* add_sens f1 <{[>false]}> (add_sens f2 <{[>true]}> base_sens)*)
  | e 1 1 => M.place f1 <{[>true]}> (M.place f2 <{[>false]}> (M.NewMap (default l_false)))(* add_sens f1 <{[>true]}> (add_sens f2 <{[>false]}> base_sens)*)
  | e 1 _ => M.place f1 <{[>false]}> (M.place f2 <{[>true]}> (M.NewMap (default l_false))) (*add_sens f1 <{[>false]}> (add_sens f2 <{[>false]}> base_sens)*)
  | e _ _ => M.place f1 <{[>true]}> (M.place f2 <{[>false]}> (M.NewMap (default l_false)))(* add_sens f1 <{[>true]}> (add_sens f2 <{[>false]}> base_sens)*)
  end.

(*Expression equivalent to formula*)
Definition exp_main: exp := 
<{app exchange $(false) (fun fun_ex[old] {app b_or $(sensor f2) (app b_and $(sensor f1) (app nfold $ (b_or) (old) (old)$)$ )$ }) $ }> .


Definition test_exp_main: exists a b, <[ 0 | sensorMap (e 0 0) | vt_end | exp_main ]> ==>
<[ a | b ]>.
Proof. 
eexists. eexists.  unfold exp_main. Admitted. 
(* device_tac. 
Qed. *)

(** Formula*)
Inductive Formula:Type := 
| T : Formula
| F : Formula 
| ES : Formula -> Formula -> Formula
| Sensor : string -> Formula.  
 
Fixpoint f_eq (f_0:Formula) (f_1:Formula) := 
match (f_0,f_1) with
| (T,T) => true
| (F,F) => true
| (ES f_a0 f_b0 , ES f_a1 f_b1 ) => (f_eq f_a0 f_a1) && (f_eq f_a0 f_a1)
| _ => false
end.

Definition to_b (w:STV_el) := 
match w with 
| net_w_el ev <{[>true]}> => true
| _ => false
end.


(*Formula evaluation on event structure*)
Fixpoint aes_formula_e (f:Formula) (ev:event) (es_s:s_net) (es_R:R_net) (oldSTV:STV): STV_el :=
match f with 
| T => net_w_el ev <{[>true]}>
| F => net_w_el ev <{[>false]}>
| ES f_0 f_1 =>  if( to_b (aes_formula_e f_1 ev es_s es_R oldSTV) ) then net_w_el ev <{[>true]}> else 
                 if( to_b (aes_formula_e f_0 ev es_s es_R oldSTV) ) then
                  (if (
                    (fix check_all (source_stv:STV):=
                    match source_stv with
                    | cons (net_w_el ev_s result) next => if (containsR (forward ev_s ev) es_R)
                                                          then (to_b (net_w_el ev_s result) || check_all next)  
                                                          else check_all next
                    | nil => false
                    end) oldSTV) then net_w_el ev <{[>true]}> else net_w_el ev <{[>false]}> )
                 else net_w_el ev <{[>false]}>
| Sensor s => net_w_el ev (M.lookup s (es_s ev))
end.  

Fixpoint aes_formula (f:Formula) (es_E:E_net) (es_R:R_net) (es_d:d_net) (es_s:s_net) : STV :=
match es_E with
 | cons ev next => let x:=aes_formula f next es_R es_d es_s  in  (aes_formula_e f ev es_s es_R x) :: x
 | nil => nil
end.

Lemma example_lemma : exists (stv:STV) (vts:vt_net) , 
stv = (aes_formula (ES (Sensor "f1"%string) (Sensor "f2"%string)) eventList messageList deviceMap sensorMap)  /\ 
netI (aes eventList messageList deviceMap sensorMap) <{exp_main}> |=> netO stv vts.
Proof.
eexists. eexists. split.  
- simpl. auto.
- Admitted. 
(* net_tac.
Qed. *)
 



