

Module Type Game.
  Parameter player : Set.   (* The players *)
  Parameter state : Set.    (* What the board looks like *)
  Parameter start : state.  (* How to set it up for a new game *)
  
  (* The set of information potentially available to a player *)
  Parameter observable : player -> Set.
  
  (* For each state, all the information available to a player at that state *)
  Parameter get_observable : state -> forall p : player, observable p.
  
  (* At each state of the game, each player has to make a decision depending *)
  (* on what he can observe of that state *)
  Parameter decision : forall p : player, observable p -> Set.
  
  (* The rules decide the next state of the game from the decisions of *)
  (* all players decisions *)
  Parameter rules : forall s : state,
    (forall p:player, decision p (get_observable s p)) ->
    state.
End Game.  

Module BasicProperties (G : Game).
  Import G.

  Definition player_decision_space (s:state) (p:player) : Set :=
    decision p (get_observable s p).
    
  Definition decision_space (s:state) : Set :=
    forall (p:player), player_decision_space s p.
  
  Definition strategy (p:player) : Set :=
    forall (h:list (observable p)) (o:observable p), decision p o.
  
  Definition memoryless (p:player) (s:strategy p) : Prop :=
    exists (f:(forall (o:observable p), decision p o)),
    forall (h:list (observable p)), s h = f.
  
  Definition looping_state (s:state) : Prop :=
    forall (dec : decision_space s), rules s dec = s.
  
  Definition decisionless_state_player (s:state) (p:player) : Prop :=
    not (inhabited (player_decision_space s p)).
  
  Definition decisionless_state (s:state) : Prop :=
    not (inhabited (decision_space s)).

  Lemma decisionless_is_looping :
    forall s:state, decisionless_state s -> looping_state s.
  Proof.
    unfold decisionless_state. intros.
    unfold looping_state. intros.
    destruct H.
    exact (inhabits dec).
    Qed.
  
    
End BasicProperties.



Module Type WinnableGame (Import G : Game).
  Module BP := BasicProperties G.
  Import BP.
  Parameter winner : state -> option player.
  Axiom winning_is_looping : Prop :=
    forall s:state, winner
End WinnableGame.


Module Type CompleteInformationGame (Import G : Game).
  Parameter deduce_state : forall (p:player), observable p -> state.
  (* Function allowing each player to infer the state from observable. *)
  
  Axiom deduce_is_inv_obs : forall (p:player) (s:state), deduce_state p (get_observable s p) = s.
  (* Proof that the state inferred is always correct. *)
  
End CompleteInformationGame.


