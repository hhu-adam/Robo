import Game.Levels.Shade.L05_Closure_minimal

World "Shade"
Level 6

Title ""

Introduction
"
"

open Set

/-- `csSup_mem_closure (hs : s.Nonempty) (B : BddAbove s) : sSup s ∈ closure s` -/
TheoremDoc csSup_mem_closure as "csSup_mem_closure" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hf : Continuous f) (hne : s.Nonempty)
    (hbd : BddAbove s) (hs : s ⊆ {x | f x ≤ c}) : f (sSup s) ≤ c := by
  Hint "[Hint cssupcl] For a nonempty set bounded above, `sSup s` lies in the closure of
    `s`.  That is `csSup_mem_closure`."
  have h1 : sSup s ∈ closure s := csSup_mem_closure hne hbd
  Hint "The closure of `s` is contained in the closed sublevel set `f x ≤ c` — combine
    `closure_minimal` with `isClosed_le`."
  have h2 : closure s ⊆ {x | f x ≤ c} := by
    apply closure_minimal hs
    apply isClosed_le
    · fun_prop
    · fun_prop
  Hint "Now `h2 h1` says that `sSup s` lies in the sublevel set, which is exactly the goal."
  apply h2 h1

Conclusion
"Excellent.  Combining all three theorems, the bound `f x ≤ c` on `s` passes to its
supremum: `f (sSup s) ≤ c`."

NewTheorem csSup_mem_closure

TheoremTab "Topology"
