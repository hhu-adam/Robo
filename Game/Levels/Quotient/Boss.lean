import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Sum


World "Quotient"
Level 100

Title "Quotient"

Introduction
"
Any function `f : A → B` can be factored into three functions as `f = m ∘ i ∘ q` where `q` is a surjection, `i` is a bijection, and $m$ is an injection.
"

open Set Function


Statement (f : A -> B) :
    ∃ (q : A -> C) (i : C -> D) (m : D -> B), Surjective q ∧ Bijective h ∧ Injective i ∧ f = m ∘ i ∘ q := by
  sorry
