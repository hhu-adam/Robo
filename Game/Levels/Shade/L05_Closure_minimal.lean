import Game.Levels.Shade.L04_IsClosed_le

World "Shade"
Level 5

Title ""

Introduction
"
"

open Set

/-- `closure_minimal (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t` -/
TheoremDoc closure_minimal as "closure_minimal" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hf : Continuous f)
    (hs : s ⊆ {x | f x ≤ c}) : closure s ⊆ {x | f x ≤ c} := by
  Hint "[Hint clmin] `closure s` is the smallest closed set containing `s`.  Apply
    `closure_minimal`; it asks for `s ⊆ ...` and that the target set is closed."
  apply closure_minimal
  · assumption
  Hint (hidden := true) "The remaining goal is that the sublevel set `f x ≤ c` is closed —
    that is `isClosed_le`."
  apply isClosed_le
  · assumption
  · fun_prop

Conclusion
"Perfect.  Since the target set is closed and contains `s`, it contains `closure s` too."

NewTheorem closure_minimal

/-- -/
DefinitionDoc closure as "closure" in "Topology"
NewDefinition closure

TheoremTab "Topology"
