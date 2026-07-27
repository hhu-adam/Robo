import Game.Levels.Aquarium.L05_IsClosed_le

World "Aquarium"
Level 6

Title ""

Introduction "Intro Aquarium L06"

open Set

/---/
TheoremDoc closure_minimal as "closure_minimal" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hf : Continuous f)
    (hs : s ⊆ {x | f x ≤ c}) : closure s ⊆ {x | f x ≤ c} := by
  Hint "[Hint clmin] `closure s` is the smallest closed set containing `s`.  Apply
    `closure_minimal`; it asks for `s ⊆ …` and that the target set is closed."
  apply closure_minimal
  · assumption
  Hint (hidden := true) "The remaining goal is that the sublevel set `f x ≤ c` is closed —
    that is `isClosed_le`."
  apply isClosed_le
  · assumption
  · fun_prop

Conclusion "Conclusion Aquarium L06: Since the target set is closed and contains `s`, it also contains
`closure s`."

NewTheorem closure_minimal
NewDefinition closure

TheoremTab "Topology"
