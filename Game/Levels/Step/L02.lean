import Game.Metadata

World "Step"
Level 2

Introduction "Intro Step L02: Vectors are functions, we define their addition pointwise."

Statement : ![1, 1 / 2] + ![- (1 : ℝ), 1 / 2] = ![0, 1] := by
  Branch
    simp
    ring
  funext i
  fin_cases i
  · simp
    ring
  · simp
    ring

NewTactic fin_cases
