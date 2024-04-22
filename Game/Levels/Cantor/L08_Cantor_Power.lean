import Game.Metadata


import Game.Levels.Cantor.L02_IsFixedPt_not
import Game.Levels.Cantor.L07_fixedPoints_Cantor

World "Cantor"
Level 7

Title "Cantor"

Introduction
"
Cantor's famous theorem states that there is no surjective function from a set to its power set.

In this level you show prove a type-theoretic formulation of this theorem.

"

open Set Function

theorem Cantor_power {A : Type*} : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  intro h
  apply no_fixedpoints_of_not
  -- JE: might be cumbersome. I just left it here for the moment for reference.
  let g : A → A → Prop := fun (a b : A) => (b ∈ f a)
  apply cantor_diagonal g h (fun x => ¬x)
