import Game.Metadata.Tactic.ByCases
import Mathlib

-- Note: In the game `tactic.hygienic` is always `false`
-- set_option tactic.hygienic false

set_option hygiene false


/-- Ensure we get unhygienic names. -/
example : A ∨ ¬ A := by
  by_cases A
  · left
    exact h -- make sure we can use unhygienic names
  . right
    exact h

/-- Ensure existing hyps are not overwritten. -/
example (h : 1 < 5) : A ∨ ¬ A := by
  by_cases A
  · left
    guard_hyp h : 1 < 5
    guard_hyp h_1 : A
    exact h_1
  . right
    guard_hyp h : 1 < 5
    guard_hyp h_1 : ¬ A
    exact h_1

set_option tactic.hygienic true

/-- In the hygienic case, there should be no accessible `h`. -/
example : A ∨ ¬ A := by
  by_cases A
  · left
    fail_if_success exact h
    assumption
  . right
    fail_if_success exact h
    assumption
