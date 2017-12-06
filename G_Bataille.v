

Require Import Game.
Require Import BaseGame.
Require Import TurnGame.



Definition card_value:Type := { v:nat | (v >= 2 /\ v <= 14) }.
Inductive card_suit :Type := | heart:card_suit | club:card_suit | diamond:card_suit | spades:card_suit.
Definition card:Type := card_value * card_suit.





Definition bounded_nat (bound:nat) : Type := {x:nat | x < bound}.
Definition get_nat (bound:nat) (x:bounded_nat bound) :=
  match x with
  | exist _ n _ => n
  end.
