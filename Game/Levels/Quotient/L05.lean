import Game.Metadata
import Game.Levels.Quotient.L04

World "Quotient"
Level 5

open FiniteSets

Introduction "Intro Quotient L05"

/-- Bundle a finite type as an element of `FiniteSets`. -/
def FiniteSets.of (α : Type) [Finite α] : FiniteSets := ⟨α, ‹_›⟩

Statement : ∀ n, ∃ (s : FiniteSets), Nat.card s = n := by
  intro n
  Hint "[Hint q5real] Every number has to be realised as the size of *some* finite set, so you
    get to choose one. The standard set with `{n}` elements is `Fin {n}`, and `FiniteSets.of`
    bundles a finite type together with its finiteness proof into an element of `FiniteSets`."
  Hint (hidden := true) "[Hint q5fin] So `use of (Fin {n})`."
  use (of (Fin n))
  Hint (hidden := true) "[Hint q5simp] `simp [of]` unfolds the bundle and does the counting."
  simp [of]

/---/
DefinitionDoc FiniteSets.of as "FinisetSets.of" in "Quotient"
