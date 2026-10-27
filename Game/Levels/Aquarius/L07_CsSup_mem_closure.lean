import Game.Levels.Aquarius.L06_Closure_minimal

World "Aquarius"
Level 7

Title ""

Introduction
"Intro Aquarius 7: If the values of some continuous function `f` on a non-empty set `s` are bounded by
 a constant `c`, then its value at the supremum of s is also bounded by c."

open Set

/---/
TheoremDoc csSup_mem_closure as "csSup_mem_closure" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hf : Continuous f) (hne : s.Nonempty)
    (hbd : BddAbove s) (hs : s ⊆ {x | f x ≤ c}) : f (sSup s) ≤ c := by
  Hint "[Hint cssupcl] `s` is a set that is bounded above, and on which `f` only takes values at most `c`.
    Need to show that f is also at most c at `sSup s`.
    Use new theorem `csSup_mem_closure`. Formulate this separately with `have`:
    ```
    have h := csSup_mem_closure hne hbd
    ```"
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
  have h := csSup_mem_closure hne hbd
  Hint (hidden := true) "[Hint l6a3i] The closure of `s` is contained in `\{x | f x ≤ c}`.
    Combine `closure_minimal` with `isClosed_le` as in the previous level."
  have h2 : closure s ⊆ {x | f x ≤ c} := by
    Hint "[Hint w5pc3] Good intermediate statement to try to prove."
    apply closure_minimal hs
    apply isClosed_le
    · fun_prop
    · fun_prop
  Hint (hidden := true) "Now `h2 h` says that `sSup s` lies in the sublevel set,
    which is exactly the goal."
  apply h2 h

Conclusion "Conclusion Aquarius L07: Combining all three theorems, the bound `f x ≤ c` on `s` passes
to its supremum: `f (sSup s) ≤ c`."

NewTheorem csSup_mem_closure

TheoremTab "Topology"
