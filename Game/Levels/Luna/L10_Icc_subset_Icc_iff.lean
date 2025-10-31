import Game.Metadata

World "Luna"
Level 10

Title ""

/-
Introduction "
**Ritha** (*zu Lina*):  Bitte, lass mich doch auch noch eine Frage stellen …

**Lina**:  Okay, eine einzige …  Aber nicht wieder zu `omega`!

Ritha macht große Augen und sieht Lina flehend an.

**Lina**:  Wenns *unbedingt* sein muss.  Aber mach schnell! Wir haben jetzt wirklich keine Zeit mehr!
"
-/
Introduction "Intro Luna L10: Use `omega` again"

/---/
TheoremDoc Finset.Icc_subset_Icc_iff as "Icc_subset_Icc_iff" in "≤"
-- Note that mathlib's theorem is more general; here we restrict to ℕ

namespace Finset
Statement Icc_subset_Icc_iff (a₁ b₁ a₂ b₂ : ℕ) :
a₁ ≤ b₁ →  (Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂) := by
  -- unfold Icc -- optional
  /-
  Hint (hidden := true) "
    **Robo**: Vielleicht hilft hier mal wieder `subset_iff`.  Und wenn gar nichts geht, probier mal `simp`.
    "
  -/
  Hint "Try subset_iff`, `simp`"
  rw [subset_iff]
  simp
  intro h₁
  -- omega -- still fails here
  constructor
  · -- omega -- still fails here
    intro h
    /-
    Hint (hidden := true) "
      **Robo**:  Die Annahme `{h}` musst du sicherlich irgendwie ausnutzen.
      Du könnest `{h}` zum Beispiel auf die Ungleichung `a₁ ≤ b₁` oder auf `a₁ ≤ a₁` anwenden!
      (Die Ungleichung `a₁ ≤ a₁` formulierst du am besten mit `have` aus.)
    "
    -/
    Hint (hidden := true) "Use assumption `{h}`. E.g. apply `{h}` onto `a₁ ≤ b₁` or `a₁ ≤ a₁`.
    Formulate `a₁ ≤ a₁` using `have`"
    apply h at h₁
    have : a₁ ≤ a₁ := by rfl  -- briefly introduced in Implies, so that Luna does not depend on Spinoza
    apply h at this
    omega
  · omega

-- Conclusion ""
Conclusion "Conclusion Luna L10"
