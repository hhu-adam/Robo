import Game.Levels.Cauchy.L10

World "Cauchy"
Level 11


open scoped ContDiff
namespace Real

Introduction "Intro Cauchy L11"

Statement : ContDiff ℝ ∞ exp := by
  Hint "[Hint sm10bgf] `ContDiff ℝ ∞` means *smooth*: differentiable arbitrarily often.
    By new theorem `contDiff_of_differentiable_iteratedDeriv` it suffices to show that every
    iterated derivative is differentiable. For `exp` this is easy, since every derivative of
    exp is exp itself."
  Hint (strict := true) (hidden := true) "[Hint sm10ih] First establish
    `∀ m, iteratedDeriv m exp = exp` by induction."
  have h : ∀ m, iteratedDeriv m exp = exp := by
    intro m
    induction m with n ih
    · apply iteratedDeriv_zero
    · funext x
      rw [iteratedDeriv_succ, ih]
      Hint (hidden := true) "[Hint sm10hd] Remember the new theorem `HasDerivAt.deriv`
        and the old theorem `hasDerivAt_exp`."
      apply HasDerivAt.deriv
      apply hasDerivAt_exp
  Hint (strict := true) "[Hint sm10cd] By `{h}`, every iterated derivative of `exp` is exp
    itself. A function is Cauchy as soon as all of its iterated derivatives are differentiable,
    so it only remains to see that exp is differentiable."
  Hint (hidden := true) "[Hint sm10df] Apply the new theorem `contDiff_of_differentiable_iteratedDeriv`."
  apply contDiff_of_differentiable_iteratedDeriv
  Hint "[Hint yctv9] This now looks unnecessarily complicated.

  If you apply `contDiff_of_differentiable_iteratedDeriv` to `ContDiff ℝ N f` for some number `N`,
  then naturally your goal becomes
  ```
   ∀ (m : ℕ), m ≤ N → Differentiable ℝ (iteratedDeriv m f)
  ```
  – you need to show that all `m`-th derivatives up to `m = N` exist.
  Here, however, `N` is `∞`, or the “top” (`⊤`) of the ordered set `ℕ∞` (the natural numbers with infinity),
  and the assumption `m ≤ ⊤` is vacuous.  The upward arrow denotes the inclusion of `ℕ` into `ℕ∞`.
  You can just ignore all of this."
  intro m hm
  clear hm
  rw [h]
  intro x
  Hint "[Hint sm10da] Apply the new theorem `HasDerivAt.differentiableAt`."
  apply HasDerivAt.differentiableAt (hasDerivAt_exp x)

/---/
TheoremDoc contDiff_of_differentiable_iteratedDeriv as "contDiff_of_differentiable_iteratedDeriv"
  in "Function"
/---/
TheoremDoc HasDerivAt.differentiableAt as "HasDerivAt.differentiableAt" in "Function"

NewTheorem contDiff_of_differentiable_iteratedDeriv HasDerivAt.differentiableAt

NewDefinition ContDiff
