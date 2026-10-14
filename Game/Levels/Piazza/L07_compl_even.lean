import Game.Metadata

World "Piazza"
Level 7

Title ""

Introduction "Intro Piazza 7: Can write `(univ \\ A)` in a nicer way."

open Set

Statement :
    {(n : ℕ) | Even n}ᶜ  = {n | Odd n} := by
  Hint "[Hint yctv9] `Aᶜ` means complement of `A`, i.e. `(univ \\ A)`."
  Hint (hidden := true) "[Hint wjedv] Try `ext`"
  ext i
  Hint (hidden := true) "[Hint uww7c] Perform `simp` again"
  simp

NewDefinition Set.compl
TheoremTab "Set"

Conclusion "Conclusion Piazza L07."
