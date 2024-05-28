import Game.Metadata


World "Symmetric Square"
Level 4

Title "Quotient Equal"

Introduction
"
We have already observed that if `a ≈ b`, then `⟦a⟧ = ⟦b⟧`. The converse is also true, and
is witnessed by `Quotient.eq`.

Therefore, we have the following logical equivalence:

```
⟦x⟧ = ⟦y⟧ ↔ x ≈ y
```
This is witnessed by `Quotient.eq`.

"

attribute [local instance] Sym2.Rel.setoid

Statement {p q : ℤ × ℤ} (h : (⟦ p ⟧ : Sym2 ℤ)  = ⟦ q ⟧) : p.1 + p.2 = q.1 + q.2 := by
    simp [Quotient.eq] at h
    cases h
    · simp
    · simp
      simp [add_comm]

NewTheorem Quotient.eq
TheoremTab "Quotient"
