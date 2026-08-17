import Game.Metadata

World "Iso"
Level 4

/-
Introduction
"
In this level you show that there every bijection gives rise to an equivalence.
"
-/
Introduction "Intro Iso L04"

open Function

Statement {A B : Type} (f : A ≃ B) : Bijective f.toFun := by
  constructor
  · Branch
      intro a₁ a₂ h
      simp [congr_arg f.invFun]
    apply Equiv.injective
  · apply RightInverse.surjective f.right_inv

/---/
TheoremDoc Function.RightInverse.surjective as "Function.RightInverse.surjective" in "Function"

/---/
TheoremDoc Equiv.injective as "Equiv.injective" in "Function"

NewTheorem Function.RightInverse.surjective Equiv.injective
