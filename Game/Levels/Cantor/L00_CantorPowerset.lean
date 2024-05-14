import Game.Metadata

World "Cantor"
Level 1

Title "Cantor's Diagonalargument"

Introduction
"
**Cantor**: Wusstet ihr dass es keine surjektiven Funktionen `f : A → Set A` gibt? Faszinierend
oder?

**Cantor**: Wie das geht? Hier, ist eine kleine Hilfe:
"

Conclusion ""

open Set Function

-- the following implies `cantor_power` but not vice versa.
-- maybe add this before L01_CantorPowerSet
Statement cantor_helper (f : A → Set A) : ¬ ∃ (a : A), f a = { x | x ∉ f x } := by
  Hint "**Robo**: Denk daran, dass `mem_setOf` aus `Set` irgendwann hilfreich sein wird."
  Branch
    push_neg
    intro _a
    by_contra _ha

  by_contra h
  rcases h with ⟨a, ha⟩
  Hint (strict := true) "**Du**: Ich denke eine Fallunterscheidung auf `{a} ∈ {f} {a}` könnte sinnvoll sein."
  Hint (hidden := true) (strict := true) "**Robo**: Das wäre `by_cases h₁ : {a} ∈ {f} {a}`."
  by_cases h₁ : a ∈ f a
  · Hint "**Robo**: Mach mal mit `suffices : {a} ∉ {f} {a}` weiter!"
    suffices : a ∉ f a
    · contradiction
    rw [ha] at h₁
    rw [mem_setOf] at h₁
    assumption
  · apply h₁
    rw [ha]
    rw [mem_setOf]
    assumption

TheoremTab "Set"
