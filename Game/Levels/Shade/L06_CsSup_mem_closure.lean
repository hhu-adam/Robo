import Game.Levels.Shade.L05_Closure_minimal

World "Shade"
Level 6

Title ""

Introduction
"[Intro]
 If the values of some continuous function `f` on a non-empty set `s` are bounded by a constant `c`,
 then the value its value of the supremum of the set is also bounded by the same constant.
"
/- COMMENT
The intro should generally include some natural language summary of what the Statement says.
Here, I've deliberately mentioned each of `f`, `s` and `c` *exactly once*, just to have them
available as variables (§0: f, §1: s, §2: c) when writing the "translation".
-/

open Set

/-- `csSup_mem_closure (hs : s.Nonempty) (B : BddAbove s) : sSup s ∈ closure s` -/
TheoremDoc csSup_mem_closure as "csSup_mem_closure" in "Topology"

Statement {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hf : Continuous f) (hne : s.Nonempty)
    (hbd : BddAbove s) (hs : s ⊆ {x | f x ≤ c}) : f (sSup s) ≤ c := by
  Hint "[Hint cssupcl] For a nonempty set bounded above, `sSup s` lies in the closure of
    `s`.  That is `csSup_mem_closure`.
    Formulate this separately with `have`."
  Branch
    /- TODO
    Add some Hints to this alternative solution.
    -/
    suffices : sSup s ∈ { x : ℝ | f x ≤ c }
    · simp at this
      assumption
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
