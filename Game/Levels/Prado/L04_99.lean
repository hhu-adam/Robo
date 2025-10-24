import Game.Metadata
import Game.Levels.Prado.L03_even_iff_two_dvd

World "Prado"
Level 4

Title ""

/-
Introduction
"Guino wirkt inzwischen ein wenig irritiert, dass ihr gar keinen Augen für sein tolles Museum habt.
Er fühlt sich ignoriert. Um eure Aufmerksamkeit zu bekommen, gibt er euch folgende Aufgabe.
"
-/
Introduction "`INTRO` Intro Prado L04"

namespace Nat

Statement : ∃ p : ℕ, Prime p ∧ p ∣ 99 := by
  use 11
  decide

TheoremTab "ℕ"
