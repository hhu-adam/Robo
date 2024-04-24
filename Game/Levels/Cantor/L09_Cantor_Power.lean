import Game.Metadata


import Game.Levels.Cantor.L02_IsFixedPt_not
import Game.Levels.Cantor.L08_fixedPoints_Cantor

World "Cantor"
Level 9

Title "Cantor"

Introduction
"
Cantor's famous theorem states that there is no surjective function from a set to its power set.

In this level you show prove a type-theoretic formulation of this theorem.

"

open Set Function

Statement cantor_power {A : Type*} : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  Hint (hidden := true) "Widerspruch."
  by_contra h
  Branch
    apply no_fixedpoints_of_not -- Lvl 2
    Branch
      -- Mathlib states one should not use the fact that `Set A` is `A → Prop`. Instead
      -- one should use `(· ∈ ·)` and `setOf`. This would looks like the following:
      let g : A → A → Prop := fun (a b : A) => (b ∈ f a)
      apply cantor_diagonal g h (fun x => ¬x)
    Branch
      apply cantor_diagonal f h (fun x => ¬x)
    apply cantor_diagonal -- Lvl 7
    assumption
  Hint "Überleg mal, wie man `cantor_diagonal` von vorhin verwenden kann."
  Hint (hidden := true) "Zum Beispiel mit `apply cantor_diagonal at {h}`!"
  apply cantor_diagonal at h
  Hint "Welche Funktion `Prop → Prop` kennst du denn die keinen Fixpunkt hat?"
  Hint (hidden := true) "Wie wäre es mit `fun (A : Prop) ↦ ¬ A`?"
  let s := (¬ ·)
  have hs := h s
  have n_hs := no_fixedpoints_of_not
  contradiction


TheoremTab "Function"
