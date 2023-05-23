From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import sensor_state.
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
From AC Require Import network_semantics.
From AC Require Import tactics.
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


Definition eventList: E_net := (e 0 1) :: (e 1 1) :: (e 2 1) :: (e 0 2) :: (e 1 2) :: (e 2 2) :: (e 0 0) :: (e 1 0) :: (e 2 0) :: nil.

Definition messageList: R_net := forward (e 0 0) (e 0 1) :: forward (e 0 0) (e 1 1) :: forward (e 1 0) (e 1 1) ::
forward (e 2 0) (e 1 1) :: forward (e 2 0) (e 2 1) :: forward (e 0 1) (e 0 2) :: forward (e 0 1) (e 2 2) ::
forward (e 1 1) (e 0 2) :: forward (e 1 1) (e 1 2) :: forward (e 1 1) (e 2 2) :: forward (e 2 1) (e 0 2) :: 
forward (e 2 1) (e 2 2) :: nil.

Definition deviceMap (e:event): nat :=  match e with | (e id n) => id end.

Definition sensorMap (ev:event): sensor_state := 
match ev with 
| e 0 0 => add f1 <{[>false]}> (add f2 <{[>true]}> base)
| e 0 1 => add f1 <{[>true]}> (add f2 <{[>false]}> base)
| e 0 2 => add f1 <{[>false]}> (add f2 <{[>true]}> base)
| e 1 1 => add f1 <{[>true]}> (add f2 <{[>false]}> base)
| e 1 _ => add f1 <{[>false]}> (add f2 <{[>false]}> base)
| e _ _ => add f1 <{[>true]}> (add f2 <{[>false]}> base)
end.

Definition exp_main: exp := 
<{app exchange $(false) (fun fun_ex[old] {app b_or $(sensor f2) (app b_and $(sensor f1) (app nfold $ (fun fun_or_x[x] {fun fun_or_y[y] {app b_or $x y$} }) (old) (false)$)$ )$ }) $ }> .


Definition test_exp_main: exists a b, <[ 0 | sensorMap (e 0 0) | vt_end | exp_main ]> ==>
<[ a | b ]>.
Proof. 
eexists. eexists.  unfold exp_main. device_tac.
Qed.


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

Definition to_b (w:nvalue) := 
match w with
| <{[>true]}> => true
| _ => false
end.

(*

 
Print aes_formula_e.  

Fixpoint aes_formula_ev (f:formula) (es_s:s_net) (es_R:R_net) {struct f}: event -> E_net -> E_net -> nvalue :=
fix dsa  (ev:event) (es_E_0:E_net) (es_E_1:E_net) {struct es_E_1}:  nvalue :=
match f with 
| T => <{[>true]}>
| F => <{[>false]}>
| ES f_0 f_1 => if( to_b (aes_formula_ev f_1 es_s es_R ev nil es_E_1) ) then <{[>true]}> else 
                if( to_b (aes_formula_ev f_0 es_s es_R ev nil es_E_1) ) then
                (if ((
                  fix check_all (explored:E_net) (remaining:E_net) : bool :=
                  match remaining with
                  | cons ev0 next => ( to_b (dsa ev0 explored next)  ) || (check_all (cons ev explored) next)
                  | nil => false
                  end 
                ) nil (es_E_0++es_E_1) ) then  <{[>true]}> else <{[>false]}> )else <{[>false]}> 
| Sensor s => (es_s ev) s  
end. 


Fixpoint aes_formula (f:formula) (es_E:E_net) (es_R:R_net) (es_d:d_net) (es_s:s_net) (oldSTV:STV) : STV :=
match es_E with
 | cons ev next => aes_formula f next es_R es_d es_s (add_STV ev (aes_formula_e f ev es_s es_R) oldSTV)
 | nil => oldSTV
end. 


*)



Fixpoint aes_formula_e (f:formula) (ev:event) (es_s:s_net) {struct f} : R_net -> nvalue :=
fix aes_formula_e_R (es_R:R_net) {struct es_R}: nvalue :=
match f with 
| T => <{[>true]}>
| F => <{[>false]}>
| ES f_0 f_1 => if( to_b (aes_formula_e f_1 ev es_s es_R) ) then <{[>true]}> else 
                if( to_b (aes_formula_e f_0 ev es_s es_R) ) then
                (match es_R with
                  | cons (forward e0 e1) next =>  
                    if (equalsEv e1 ev) then 
                         (if ()  (aes_formula_e_R next) )
                    else <{[>false]}>
                  | nil => <{[>false]}>
                end) else <{[>false]}>
| Sensor s => (es_s ev) s
end.

Fixpoint aes_formula (f:formula) (es_E:E_net) (es_R:R_net) (es_d:d_net) (es_s:s_net) (oldSTV:STV) : STV :=
match es_E with
 | cons ev next => aes_formula f next es_R es_d es_s (add_STV ev (aes_formula_e f ev es_s es_R) oldSTV)
 | nil => oldSTV
end.

(*
Fixpoint es_e (f1:string) (f2:string) (e:event) (es_R:R_net) (es_s:s_net) :=
match es_R with
|cons r_el next => if (equalsR r_el rel) then true else (containsR rel next)
|nil => false 
end.

Fixpoint es_E (f1:string) (f2:string) (es_E:E_net) (es_R:R_net) (es_d:d_net) (es_s:s_net) (oldSTV:STV) {struct es_E} : STV :=
match es_E with
 | cons (e id n) next => es_E f1 f2 next es_R es_d es_s (oldSTV)
 | nil => oldSTV
end.
*)

 
Lemma one_lemma : exists (nvalueMap:event->nvalue) , 
nvalueMap= (aes_formula (ES (Sensor "f1"%string) (Sensor "f2"%string)) eventList messageList deviceMap sensorMap base_STV)  /\ 
netI (aes eventList messageList deviceMap sensorMap) eventList base_vt <{exp_main}> |=> nvalueMap .
Proof.
eexists. eexists. 
- simpl. auto. 
- eapply E_NET_R. simpl. auto. device_tac. 
eapply E_NET_R. simpl. auto. device_tac. 
eapply E_NET_R. simpl. auto. device_tac.
eapply E_NET_R. simpl. auto. device_tac.
eapply E_NET_R. simpl. auto. device_tac.
eapply E_NET_R. simpl. auto. device_tac.
eapply E_NET_R. simpl. auto. device_tac.
eapply E_NET_R. simpl. auto. device_tac.
eapply E_NET_R. simpl. auto.  device_tac. simpl.  unfold add_vt. simpl. unfold base_vt.   
eapply E_NET_0.
Qed.



