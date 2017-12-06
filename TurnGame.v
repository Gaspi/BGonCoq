
Require Import Game.
Require Import BaseGame.

Section TurnGame.

Variable g:Game.


Definition is_turn_function (turn:state g -> nat) : Prop :=
  turn (start g) = 0 /\
  forall s:state g, accessible_states g s ->
    forall dec:decision_fun g s, turn (rules g s dec) = S (turn s).



Definition is_strong_turn_function (turn:state g -> nat) : Prop :=
  turn (start g) = 0 /\
  forall s:state g,
  forall dec:decision_fun g s,
    turn (rules g s dec) = S (turn s).

Lemma strong_turn_is_turn : forall turn:state g -> nat, is_strong_turn_function turn -> is_turn_function turn.
Proof.
  intros.
  edestruct H.
  split.
  exact H0.
  intros.
  apply H1.
Qed.


Definition is_turned_game : Prop :=
  exists turn : state g -> nat, is_turn_function turn.

Definition is_strong_turned_game : Prop :=
  exists turn : state g -> nat, is_strong_turn_function turn.


Lemma strong_turned_is_turned : is_strong_turned_game -> is_turned_game.
Proof.
  intros.
  edestruct H.
  exists x.
  exact (strong_turn_is_turn x H0).
Qed.

Lemma turn_functions_coincide_on_accessible : forall t1 t2:state g -> nat, is_turn_function t1 -> is_turn_function t2 -> forall s:state g, accessible_states g s -> t1 s = t2 s.
Proof.
  intro.
  intro.
  intro.
  intro.
  edestruct H.
  edestruct H0.
  apply accessible_states_from_ind.
  rewrite H1, H3.
  auto.
  intros.
  rewrite (H2 s H5 dec).
  rewrite (H4 s H5 dec).
  rewrite H6.
  auto.
Qed.


End TurnGame.