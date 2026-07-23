import Game.Levels.Culmen.L06_Closure_minimal

World "Culmen"
Level 7

Title ""

Introduction
"Intro Culmen 7: If the values of some continuous function `f` on a non-empty set `s` are bounded by
 a constant `c`, then its value at the supremum of s is also bounded by c."

open Set

/---/
TheoremDoc csSup_mem_closure as "csSup_mem_closure" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hf : Continuous f) (hne : s.Nonempty)
    (hbd : BddAbove s) (hs : s ⊆ {x | f x ≤ c}) : f (sSup s) ≤ c := by
  Hint "[Hint cssupcl] For a nonempty set bounded above, `sSup s` lies in the closure of
    `s`.  That is `csSup_mem_closure`.  Formulate this separately with `have`."
  Branch
    suffices : sSup s ∈ { x : ℝ | f x ≤ c }
    · simp at this
      assumption
    Hint (hidden := true) (strict := true) "[Hint 9xyh5] If this is the route you want to take,
      perhaps now establish `sSup s ∈ closure s` with `have`."
    have : sSup s ∈ closure s := by
      apply csSup_mem_closure
      assumption
      assumption
    apply closure_minimal at hs
    have h_c : IsClosed { x : ℝ | f x ≤ c } := by
      apply isClosed_le
      assumption
      fun_prop
    apply hs at h_c
    apply h_c at this
    assumption
  have h1 : sSup s ∈ closure s := csSup_mem_closure hne hbd
  Hint (hidden := true) "The closure of `s` is contained in the closed sublevel set `f x ≤ c` — combine
    `closure_minimal` with `isClosed_le`."
  have h2 : closure s ⊆ {x | f x ≤ c} := by
    Hint "[Hint w5pc3] Good intermediate statement to try to prove."
    apply closure_minimal hs
    apply isClosed_le
    · fun_prop
    · fun_prop
  Hint (hidden := true) "Now `h2 h1` says that `sSup s` lies in the sublevel set,
    which is exactly the goal."
  apply h2 h1

Conclusion "Conclusion Culmen L07: Combining all three theorems, the bound `f x ≤ c` on `s` passes
to its supremum: `f (sSup s) ≤ c`."

NewTheorem csSup_mem_closure

TheoremTab "Topology"
