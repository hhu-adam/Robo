import Game.Levels.Smooth.L05

World "Smooth"
Level 6

open Polynomial

Introduction "Intro Smooth L06"

/- The derivative of `x ↦ p(-x⁻¹)` at `x ≠ 0`, obtained from the chain rule. -/
Statement (p : ℝ[X]) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun x ↦ p.eval (-x⁻¹))
      ((derivative p).eval (-x⁻¹) * (-1 * -(x ^ 2)⁻¹)) x := by
  Hint (strict := true) "[Hint dxq1] `HasDerivAt f f' x` means that `f` has derivative `f'` at the point `x`.
    So goal is to compute derivative of triple composition `p ∘ neg ∘ inv` using chain rule,
    and express is using the formal derivative `derivative p` of `p`.

    The derivative of each factor is known:

    - `p.hasDerivAt x` says that p has derivative `(derivative p).eval x` at x
    - `hasDerivAt_neg x` says the derivative of `x ↦ -x` at x is `-1`
    - `hasDerivAt_inv hx`, where `hx` is the assumption `x ≠ 0`, computes the derivative of `x ↦ x⁻¹`

    And the chain rule is called `HasDerivAt.comp`.

    Use the following trick to piece this together.
    Load the statement of `hasDerivAt_inv hx` into your context with:
    ```
    have h_inv := hasDerivAt_inv hx
    ```
    "
  Branch
    /- An alternative, backward approach in which the proof assistant actually assists.
       However, this only works by chance, when the derivate is already written in the correct form.
       It fails in the boss level 08, so this approach should *not* be introduced here. -/
    have h_comp : (fun x ↦ p.eval (-x⁻¹)) = p.eval ∘ Neg.neg ∘ Inv.inv := by
      rfl
    rw [h_comp]
    apply HasDerivAt.comp x
    · apply p.hasDerivAt
    · apply HasDerivAt.comp x
      · apply hasDerivAt_neg
      · apply hasDerivAt_inv hx
  have h_inv := hasDerivAt_inv hx
  Hint (strict := true) "[Hint szsqh] Now similarly for `neg`."
  Branch
    have := hasDerivAt_neg x
    Hint "[Hint 3cbyh] That's not what you want. If you want to apply the chain rule,
      you will need the derivate of `neg ∘ inv` at a different point than `x`."
  have h_neg := hasDerivAt_neg x⁻¹
  Hint (strict := true) "[Hint 9uibu] Excellent!  Now apply the chain rule.
    ```
    have h_neginv := HasDerivAt.comp …
    ```
    "
  have h_neginv := HasDerivAt.comp x h_neg h_inv
  Hint (strict := true) "[Hint fir3i] Excellent.  Now proceed in a similar fashion for the
    composition with `p`."
  have h_p := p.hasDerivAt (-x⁻¹)
  clear h_neg h_inv hx
  Hint (hidden := true) "[Hint 70lg1] Now the new theorem that encodes the chain rule: `HasDerivAt.comp`"
  apply HasDerivAt.comp x h_p h_neginv

/---/
TheoremDoc HasDerivAt.comp as "HasDerivAt.comp" in "HasDerivAt"
/---/
TheoremDoc hasDerivAt_inv as "hasDerivAt_inv" in "Function"
/---/
TheoremDoc hasDerivAt_neg as "hasDerivAt_neg" in "Function"

NewTheorem HasDerivAt.comp hasDerivAt_inv hasDerivAt_neg
