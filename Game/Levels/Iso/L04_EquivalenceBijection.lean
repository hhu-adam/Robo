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
  Hint "[Hint p4wnd] The underlying function of an equivalence is bijective."
  constructor
  · Branch
      intro a₁ a₂ h
      simp [congr_arg f.invFun]
    Hint (hidden := true) "[Hint c9tzr] This is exactly `Equiv.injective`."
    apply Equiv.injective
  · Hint "[Hint x2fqm] A map that admits a right inverse is surjective, and `f.right_inv` says
    that `f.invFun` is one."
    Hint (hidden := true) "[Hint j6hlv] `Function.RightInverse.surjective` turns that into surjectivity."
    apply RightInverse.surjective f.right_inv

/---/
TheoremDoc Function.RightInverse.surjective as "Function.RightInverse.surjective" in "Function"

/---/
TheoremDoc Equiv.injective as "Equiv.injective" in "Function"

NewTheorem Function.RightInverse.surjective Equiv.injective
