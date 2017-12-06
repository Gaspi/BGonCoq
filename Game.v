
Structure Game :=
{
  player : Set;  (* The players *)
  state : Set;   (* What the board looks like *)
  start : state;  (* How to set it up for a new game *)
  
  (* The set of information potentially available to a player *)
  observable : player -> Set;
  
  (* For each state, all the information available to a player at that state *)
  get_observable : state -> forall p : player, observable p;
  
  (* At each state of the game, each player has to make a decision depending *)
  (* on what he can observe of that state *)
  decision : forall p : player, observable p -> Set;
  
  (* The rules decide the next state of the game from the decisions of *)
  (* all players decisions *)
  rules : forall s : state,
          (forall p:player, decision p (get_observable s p)) ->
            state;
}.


