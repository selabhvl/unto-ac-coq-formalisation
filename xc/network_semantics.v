From AC Require Import syntax.
From AC Require Import basics.
From AC Require Import value_tree.
From AC Require Import nvalues.
From AC Require Import big_step_semantics.
Require Import mapping.
Require Import Maps.

Require Import Bool.
Require Import String.
Require Import List.
Require Import PeanoNat.
Require Import event.

Module NetworkSemantics (Map : MAPPING).

  Module Import EventMap := Map(EventKey).
  Module Import BS := BigStepSemantics(Map).
  Include BS.

  (*Event equality function*)
  Definition equalsEv (e0:event) (e1:event) := 
  match (e0,e1) with (e id0 n0,e id1 n1) => (id0 =? id1) && (n0 =? n1) end.

  (*Relation between events (message) defined as an inductive type*)
  Inductive relation := forward : event -> event -> relation.

  (*Equality of relations*)
  Definition equalsR (r0:relation) (r1:relation) := match (r0,r1) with 
  | (forward e0_in e0_out,forward e1_in e1_out) => if ((equalsEv e0_in e1_in) && (equalsEv e0_out e1_out)) then true else false end.

  (*A list of relations*)
  Definition R_net := list relation.

  (*Function that checks if a list of relation contains a certain relation*)
  Fixpoint containsR (rel:relation) (rl:R_net) : bool :=
  match rl with 
  |cons r_el next => if (equalsR r_el rel) then true else (containsR rel next)
  |nil => false 
  end. 

  (*A d_net is a function that maps a event to a device*)
  (* Definition d_net := event -> ident. *)
  (*The returned value if a searched event doesn't exists*)
  (* Definition base_d (e:event) := 0. *)
  (*Add a event to a d_net, with respective device id*)
  (* Definition add_d (new_e:event) (new_d:ident) (old:d_net): d_net :=(fun e => if (equalsEv e new_e) then new_d else (old e)). *)
  Definition d_net := EventMap.MapOf ident.
  Definition base_d := EventMap.NewMap 0.

  (*A s_net is a function that maps a event to a sensor_state*)
  (* Definition s_net := event -> sensor_state. *)
  (*The returned value if a searched event doesn't exists*)
  (*Definition base_s (e:event) : sensor_state := BS.StringMap.NewMap (default l_fail). *)(*base_sens.  <- Original one left as comment during refactoring *)
  (*Add a event to a s_net, with respective sensor_state*)
  (* Definition add_s (new_e:event) (new_s:sensor_state) (old:s_net): s_net :=
    (fun e => if (equalsEv e new_e) then new_s else (old e)). *)
  Definition s_net := EventMap.MapOf sensor_state.
  Definition base_s := EventMap.NewMap (BS.StringMap.NewMap (default l_fail)).


  (*The augmented event structure, like defined in the papers*)
  Inductive AES := aes : E_net -> R_net -> d_net -> s_net -> AES.


  (*Space-time value element of list definition*)
  Inductive STV_el := net_w_el : event -> nvalue -> STV_el. 
  Definition STV := list STV_el.

  (*Value-tree network element of list definition*)
  Inductive vt_net_el := net_vt_el : event -> value_tree -> vt_net_el. 
  Definition vt_net := list vt_net_el. 


  (** Given a certain event, event structure, relations of the net, value-trees of the net and device id of the net
  Returns a value-tree environment containing the output value-tree of event happened before the given event
  *)
  Fixpoint before_event (b_e:event) (b_E:E_net) (b_R:R_net) (b_vts:vt_net) (b_d:d_net): value_tree_env := 
  match (b_E,b_vts) with 
  | (cons el0 next,cons (net_vt_el el1 vt) next_vt) => if ((containsR (forward el0 b_e) b_R) && (equalsEv el0 el1) ) then vt_el (EventMap.lookup ident el0 b_d) (vt) (before_event b_e next b_R next_vt b_d) 
  else (before_event b_e next b_R next_vt b_d)
  | (nil,nil) => vt_end
  | _ => vt_end
  end.


  (** A variant of the function described before but with Optional output*)
  Definition add_vts_el (d:nat) (vt:value_tree) (vts:value_tree_env) := vt_el d vt vts. 
  Fixpoint before_event_option (b_e:event) (b_E:E_net) (b_R:R_net) (b_vts:vt_net) (b_d:d_net): option value_tree_env := 
  match (b_E,b_vts) with 
  | (cons el0 next,cons (net_vt_el el1 vt) next_vt) => 
    if (equalsEv el0 el1) then 
        (let x:=before_event_option b_e next b_R next_vt b_d in 
        if (containsR (forward el0 b_e) b_R) then (option_map (add_vts_el (EventMap.lookup ident el0 b_d) vt) x) else (x)
        )
    else None
  | (nil,nil) => Some vt_end
  | _ => None
  end. 

  (** Input and Output network configuration
  Input conf is composed by an Augmented Event structure and an expression
  Output conf is composed by a space time value and all the value-tree evaluated in the net*)
  Inductive net_conf_in: Type := netI : AES -> exp -> net_conf_in.
  Inductive net_conf_out: Type := netO : STV -> vt_net -> net_conf_out.

  Reserved Notation "t '|=>' t'" (at level 40).
  Inductive net_val: net_conf_in -> net_conf_out -> Prop :=

  | E_NET_0 : forall (e_main:exp) (n_R:R_net) (n_d:d_net) (n_s:s_net),

  netI (aes (nil) n_R n_d n_s) e_main |=> netO nil nil


  | E_NET_R : forall (e_main:exp) (ev:event) (next:E_net) (n_R:R_net) (n_d:d_net) (n_s:s_net) (w:nvalue) 
  (next_stv:STV) (vt:value_tree) (next_vts:vt_net) (vt_env:value_tree_env),

  netI (aes next n_R n_d n_s) e_main |=> netO next_stv next_vts

  -> vt_env = before_event ev next n_R next_vts n_d 

  -> <[ EventMap.lookup ident ev n_d | EventMap.lookup sensor_state ev n_s  | vt_env | e_main ]> ==> <[ w |  vt ]> 

  -> netI (aes (cons ev next) n_R n_d n_s) e_main |=> netO (cons (net_w_el ev w) next_stv)  (cons (net_vt_el ev vt) next_vts) 

  where "t '|=>' t'" := (net_val t t').


  Definition notNone {A:Type} (op:option A) :=
  match op with
  | Some _ => true
  | None => false
  end.

End NetworkSemantics.






