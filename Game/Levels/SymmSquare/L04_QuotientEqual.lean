import Game.Metadata


World "Symmetric Square"
Level 4

Introduction
"Intro Symm L04:
We have already observed that if `a ≈ b`, then `⟦a⟧ = ⟦b⟧`. The converse is also true, and
is witnessed by `Quotient.eq`.

Therefore, we have the following logical equivalence:

```
⟦x⟧ = ⟦y⟧ ↔ x ≈ y
```
This is witnessed by `Quotient.eq`.

"

attribute [local instance] Sym2.Rel.setoid

Statement {p q : ℤ × ℤ} (h : (⟦ p ⟧ : Sym2 ℤ) = ⟦ q ⟧) : p.1 + p.2 = q.1 + q.2 := by
  Hint "[] The equivalent class `⟦x⟧` and `⟦y⟧` agree if and only if `x` and `y` satisfy the equivalence
  relation, i.e. `r x y`."
  rw [Quotient.eq] at h
  Hint "[] Try `cases h`. "
  cases h
  · ring
  · ring


TheoremTab "Quotient"
