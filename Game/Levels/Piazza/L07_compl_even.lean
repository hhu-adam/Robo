import Game.Metadata

World "Piazza"
Level 7

Title ""

Introduction "Instead of `(univ \\ A)` can also write `Aᶜ` (typed as `\\compl` or `\\^c`)."

open Set

Statement :
    {(n : ℕ) | Even n}ᶜ  = {n | Odd n} := by
  Hint (hidden := true) "[Hint cqvs] Try `ext`"
  ext i
  Hint (hidden := true) "Perform `simp` again"
  simp


NewDefinition Set.compl
TheoremTab "Set"

Conclusion "Conclusion Piazza L07: the complement `Aᶜ` is `univ \\ A`."
