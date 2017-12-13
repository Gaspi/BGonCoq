
Require Import Game.


Module Basic(G : Game).
  Import G.
  
  Definition decision_fun (s:state)  (p:player) := decision p (observable s p).
  Definition strategy     (p:player) (s:state)  := decision p (observable s p).

  Definition strategy (p:player) := forall s:state, decision p ().
  
  Definition final_state (s:state g) := forall f:decision_fun s, rules g s f = s.
  
  Definition decisionless_state (s:state g) := not (inhabited (decision_fun s)).
  
  Lemma decisionless_is_final : forall s:state g, decisionless_state s -> final_state s.
  Proof.
    intros.
    intro.
    edestruct H.
    exact (inhabits f).
  Qed.


Require Import Ensembles.
Require Import Image.

Definition empty_game := final_state (start g).

Lemma singlestate_games_are_empty : (forall s t:state g, s = t) -> empty_game.
Proof.
  intros.
  intro.
  apply H.
Qed.

Lemma decisionless_games_are_empty : (not (inhabited (decision_fun (start g)))) -> empty_game.
Proof.
  exact (decisionless_is_final (start g)).
Qed.


Inductive accessible_states_from (st:state g) : Ensemble (state g) :=
  | start_access : accessible_states_from st st
  | ind_access   : forall s:state g, accessible_states_from st s -> forall dec:decision_fun s,
      accessible_states_from st (rules g s dec).


Definition accessible_states : Ensemble (state g) := accessible_states_from (start g).

Lemma start_is_always_accessible : accessible_states (start g).
Proof.
  exact (start_access (start g)).
Qed.

Lemma empty_games_access_start_only : empty_game -> forall s:state g, accessible_states s -> s = start g.
Proof.
  intro.
  apply accessible_states_from_ind.
  auto.
  intro. intro. intro.
  replace s with (start g).
  intro.
  exact (H dec).
Qed.


Definition final_accessible_states_from (s:state g) := Union (state g) (accessible_states_from s) final_state.

Definition final_accessible_states := Union (state g) accessible_states final_state.

Definition possible_decisions (p:player g) := Im (state g) Type accessible_states (fun x => decision g x p).


Definition next_state (strat:strategy) (s:state g) := rules g s (fun p => strat p s).


Definition finite_type (A:Type) := Finite _ (Full_set A).

Definition finite_state_game    := finite_type (state g).
Definition finite_player_game   := finite_type (player g).
Definition finite_decision_game := forall s:state g, forall p:player g, finite_type (decision g s p).

Definition finite_game := Finite _ (accessible_states).

Lemma finite_state_are_finite_games : finite_state_game -> finite_game.
Proof.
  intros.
  cut (Included (state g) (accessible_states) (Full_set (state g))).
  intro.
  exact (Finite_downward_closed (state g) (Full_set (state g)) H accessible_states H0).
  intro.
  intro.
  exact (Full_intro (state g) x).
Qed.


End BaseGame.
