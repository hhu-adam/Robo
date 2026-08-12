import Game.Metadata


World "Symmetric Square"
Level 4

Introduction "Intro Symm L04"

attribute [local instance] Sym2.Rel.setoid

Statement {p q : ℤ × ℤ} (h : (⟦ p ⟧ : Sym2 ℤ) = ⟦ q ⟧) : p.1 + p.2 = q.1 + q.2 := by
  Hint "[Hint sy4qeq] The previous level went from `x ≈ y` to `⟦x⟧ = ⟦y⟧`; the converse holds
    too, so classes agree exactly when the representatives are equivalent: `⟦x⟧ = ⟦y⟧ ↔ x ≈ y`.
    That equivalence is `Quotient.eq`."
  Hint (hidden := true) "[sy4eqeh] Rewriting `{h}` with `Quotient.eq` brings you back to the pairs."
  rw [Quotient.eq] at h
  Hint (hidden := true) "[Hint sy4cs] `cases h` splits into the two ways `{p}` and `{q}` can be
    related."
  cases h
  · ring
  · ring


TheoremTab "Quotient"
