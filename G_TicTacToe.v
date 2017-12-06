Require Import Bool.

Require Import Game.
Require Import BaseGame.
Require Import TurnGame.



Inductive  coord  : Type := | t1 | t2 | t3.
Definition coord_eq (a b : coord) := match (a,b) with | (t1,t1) | (t2,t2) | (t3,t3) => true |_ => false end.

Definition coords : Type := coord * coord.
Definition coords_eq (a b:coords) := (coord_eq (fst a) (fst b)) && (coord_eq (snd a) (snd b)).

Inductive TTT_player : Type := | XPlayer | OPlayer.
Definition player_eq (a b:TTT_player) := match (a,b) with (XPlayer,XPlayer) | (OPlayer, OPlayer) => true |_ => false end. 
Definition other_player (p:TTT_player) := match p with | XPlayer => OPlayer | OPlayer => XPlayer end.

Inductive tile_state : Type := | Empty | X | O.
Definition TTT_state : Type := TTT_player * (coords -> tile_state).
Definition player_tile  (p:TTT_player) := match p with | XPlayer => O       | OPlayer => X end.

Definition TTT_choice_state (s:TTT_state) := { c:coords | snd s c = Empty }.

Definition TTT_choice (s:TTT_state) (p:TTT_player) := if player_eq p (fst s) then TTT_choice_state s else unit.


Lemma TTT_turn_player_chooses : forall s:TTT_state, TTT_choice s (fst s) = TTT_choice_state s.
Proof.
  intro.
  destruct s.
  destruct t.
  compute. auto.
  compute. auto.
Qed.


Definition get_choice_coords (s:TTT_state) (dec:forall p:TTT_player, TTT_choice s p) : TTT_choice s (fst s) :=
  dec (fst s).


Definition update_state (s:TTT_state) (c:coords) (new_val:tile_state) : TTT_state :=
  (fst s,
   fun x => if coords_eq x c then new_val else snd s x).


Definition TTT_rules (s:TTT_state) (dec:forall p:TTT_player, TTT_choice s p) : TTT_state :=
  match s with
  | (cur_player, cur_board) =>
    let cur_tile := player_tile cur_player in
    let cur_move :  dec cur_player with
    | 
    
    let cur_move :=  in
      (other_player cur_player,
       fun c => if coords_eq c cur_move then cur_tile else cur_board c)
  end.

    fun c:coords => update_state s ch .

Check TTT_rules.


Definition TTT : Game :=
  mkGame
    TTT_player
    TTT_state
    (XPlayer, fun x => Empty)
    TTT_choice
    TTT_rules.





