import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Cantor.L02_IsFixedPt_not
import Game.Levels.Cantor.L06_fixedPoints_Cantor

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
  apply cantor_diagonal f h (fun x => ¬x)
