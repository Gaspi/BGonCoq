
Require Import Game.
Require Import BaseGame.
Require Import TurnGame.

(* --------------------------------------------------------
     Nothing to do here but count...
     Don't judge, you've played it too !.
   -------------------------------------------------------- *)
Definition counting_game : Game :=
  mkGame
    True
    nat
    0
    (fun s p => unit)
    (fun s dec => S s).



Lemma counting_is_strong_turned : is_strong_turned_game counting_game.
Proof.
  compute.
  exists id.
  split.
  auto.
  intros.
  compute.
  auto.
Qed.

Lemma couting_turned_based : is_turned_game counting_game.
Proof.
  exact (strong_turned_is_turned counting_game counting_is_strong_turned).
Qed.






