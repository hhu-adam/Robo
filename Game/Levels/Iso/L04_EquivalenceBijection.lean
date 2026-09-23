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

open Function FullGrind

Statement {A B : Type} (f : A ≃ B) : Bijective f.toFun := by
  Hint "[Hint p4wnd] Given an equivalence `f`, you can access its components
    and the relevant proofs with `f.toFun`, `f.invFun`, `f.left_inv` and `f.right_inv`.
    However, it's recommended to rely on coercion and use
    - f in place of f.toFun, and
    - `f.symm` in place of f.invFun"
  Hint (hidden := true) "[Hint 6my94] Remember we proved `bijective_iff_has_inverse` a moment ago."
  rw [bijective_iff_has_inverse]
  use f.symm
  constructor
  apply f.left_inv
  apply f.right_inv
