

Module Type Game.
  Parameter player : Set.   (*  Who are the players ?      *)
  Parameter state : Set.    (*  What is the board like ?   *)
  Parameter start : state.  (*  How should we set it up ?  *)
  
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




Module RPSGame : Game.
  
  Inductive player : Set :=
  | playerA : player
  | playerB : player.
  
  Inductive moves : Set :=
  | Rock : moves
  | Paper : moves
  | Scissor : moves.

  Inductive state : Set :=
  | HandsReady : state
  | HandsDown : (player -> moves) -> state.
  
  Definition start : state := HandsReady.
  
  Definition observable (p:player) : Set := option (player -> moves).
  
  Definition get_observable (s:state) (p : player) : observable p :=
    match s with
    | HandsReady  => None
    | HandsDown obs => Some obs
    end.
  
  Definition decision (p : player) (o : observable p) : Set :=
    match o with
    | None  => moves
    | Some _ => Empty_set
    end.
  
  Definition rules (s : state) (move : forall p:player, decision p (get_observable s p)) : state.
  Proof.
    destruct s.
    simpl in move.
    exact (HandsDown move).
    exact (HandsDown m).
  Qed.
  
  Print rules.

  Eval compute in
      rules
        HandsReady
        (fun p : player =>
           match p with
           | playerA => Rock
           | playerB => Paper
           end)
  .

End RPSGame.





Module BasicProperties (Import G : Game).

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
  
  (* Difference between empty decision space and singleton decision space !!! *)
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
  
  Parameter winner : state -> option player.
  
  Definition has_winner (s : state) : bool :=
    match winner s with
    | None => false
    | Some p => true end.
  
  Definition is_winning (s : state) : Prop := exists p : player, winner s = Some p.
  
  Module BP := BasicProperties G.
  Import BP.
  
  Axiom winning_is_decisionless : forall s : state, is_winning s = true -> decisionless_state s.
  
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

