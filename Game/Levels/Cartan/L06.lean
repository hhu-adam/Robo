import Game.Metadata

World "Cartan"
Level 6

open Topology Filter

Statement {f g : ℝ → ℝ} {a : ℝ} (ha : a < 0) (h : ∀ x < 0, f x = g x) :
    f =ᶠ[𝓝 a] g := by
  Hint (strict := true) "[Hint fjpr0] First establish `∀ᶠ x in 𝓝 a, x < 0` with `have`."
  have h : ∀ᶠ x in 𝓝 a, x < 0 := by
    apply eventually_lt_nhds ha
  Hint "[Hint 4j4cl] Try `filter_upwards [{h}]`."
  filter_upwards [h]
  assumption

Conclusion "Conclusion Cartan L06:  What does `filter_upwards` do?
Suppose we have an eventual hypothesis `h₁ : ∀ᶠ x in 𝓕, p₁ x`
and an eventual goal `∀ᶠ x in 𝓕, p x`.
Then `filter_upwards [h₁]'` reduces the goal to the point-wise implication `p₁ x → p x`."


NewTactic filter_upwards
NewHiddenTactic «in»
NewDefinition Filter.EventuallyEq
