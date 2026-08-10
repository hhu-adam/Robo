import Game.Metadata

World "Hamel"
Level 2

Introduction "Intro Hamel L02"

Statement : ![1, 1 / 2] + ![- (1 : ℝ), 1 / 2] = ![0, 1] := by
  Branch
    simp
    ring
  Hint "[Hint pwadd] Both sides are functions `Fin 2 → ℝ`, and their sum is defined pointwise.
    So it is enough to compare the two sides coordinate by coordinate."
  Hint (hidden := true) "[Hint fnext] Two functions are equal if they agree on every
    argument — that is `funext`."
  funext i
  Hint "[Hint fincs] The index `{i}` has type `Fin 2`, so it is either `0` or `1`.
    You can treat these two cases separately with `fin_cases {i}`."
  fin_cases i
  · Hint (hidden := true) "[Hint lcside] Try `simp`."
    simp
    ring
  · Hint (hidden := true) "[Hint lcside] Try `simp`."
    simp
    ring

NewTactic fin_cases
