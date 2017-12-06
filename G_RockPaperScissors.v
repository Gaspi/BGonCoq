
Require Import Game.
Require Import BaseGame.

Inductive RPS_player : Type := | J1 | J2.
Inductive RPS_choice : Type := | Rock | Paper | Scissors.
Inductive RPS_state  : Type :=
  | NoWinner : RPS_state
  | Winner : RPS_player -> RPS_state.



Definition RPS_rules (s:RPS_state) (dec:RPS_player -> RPS_choice) :=
  match s with
  | Winner p => Winner p
  | NoWinner =>
    match (dec J1, dec J2) with
    | (Rock    , Scissors)
    | (Scissors, Paper)
    | (Paper   , Rock) => Winner J1
    | (Rock    , Rock)
    | (Scissors, Scissors)
    | (Paper   , Paper) => NoWinner
    | _ => Winner J2
    end
  end.

Definition RPS : Game :=
  mkGame
    RPS_player
    RPS_state
    NoWinner
    (fun s p => RPS_choice)
    RPS_rules.

(*
If the game is not done yet, forall J1 move there is a winning move for J2.
Random is not yet in this model.
Basically this holds because J1 and J2 both have access to all random variables.
*)
Lemma J2_may_always_win :
  forall s:RPS_state,
  forall d1:decision RPS NoWinner J1,
  exists d2:decision RPS NoWinner J2,
    rules RPS
          NoWinner
          (fun p => match p with | J1 => d1 | J2 => d2 end) = s.
Proof.
  Check RPS_state_ind.
  intros.
  destruct s.
  destruct d1.
  exists Rock. compute. auto.
  exists Paper. compute. auto.
  exists Scissors. compute. auto.
  destruct d1.
  destruct r.
  exists Scissors. compute. auto.
  exists Paper. compute. auto.
  destruct r.
  exists Rock. compute. auto.
  exists Scissors. compute. auto.
  destruct r.
  exists Paper. compute. auto.
  exists Rock. compute. auto.
Qed.


