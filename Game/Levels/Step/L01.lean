import Game.Metadata


World "Step"
Level 1

Introduction "Intro Step L01: An `n`-dimensional vector is a function out of `Fin n`. For instance
a real-valued vector `x : Fin n → ℝ` assigns to each coordinate `i : Fin` a scalar
`x i : ℝ`. We represent such a vector as `![x_1, …, x_n]`."

/-- `![x₀, …, xₙ₋₁]` is notation for the vector `Fin n → α` sending each index `i` to `xᵢ`.
Applying it to an index, `![a, b, c] 1`, returns that entry (`b`), so equalities between explicit
entries hold by `rfl`. -/
DefinitionDoc vecNotation as "vecNotation" in "Matrix"

Statement (a b c : ℝ) : ![a, b, c] 0 + ![a, b, c] 1 = a + b := by
  Hint (hidden := true) "[Hint s1trl] `rfl`? "
  rfl

NewDefinition vecNotation
