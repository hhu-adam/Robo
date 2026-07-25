import Game.Metadata

World "Cartan"
Level 12

open Topology Filter

Introduction "
A function `f` is *locally constant* if every point has a neighborhood on which
`f` is constant. In Mathlib this is captured by `IsLocallyConstant f`, which is
defined as: the preimage `f ⁻¹' s` of *every* set `s` is open.

Here you show that a locally constant function is *eventually* equal to its
value at `x`, for the neighborhood filter `𝓝 x`.
"

-- /---/
-- TheoremDoc IsLocallyConstant.eventually_eq as "IsLocallyConstant.eventually_eq"

Statement {f : ℝ → ℝ} {x : ℝ}
    (hf : IsLocallyConstant f) : ∀ᶠ y in 𝓝 x, f y = f x := by
  Hint (strict := true) "[Hint pissfx] The preimage of single point set \{f x} is open."
  Hint (hidden := true) "[Hint hpissfx] Establish `IsOpen (f ⁻¹' \{f x})` by `have`."
  have h : IsOpen (f ⁻¹' {f x}) := by
    apply hf
  Hint "[Hint tfuiem] Try `filter_upwards [IsOpen.eventually_mem {h} rfl]`"
  filter_upwards [IsOpen.eventually_mem h rfl]
  intro y hy
  assumption

NewDefinition IsLocallyConstant
