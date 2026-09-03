import Game.Metadata
import Game.Levels.Quotient.L03

World "Quotient"
Level 4

Introduction "Intro Quotient L04"

noncomputable section

open FiniteSets

/--
`cardMap` sends the class of a finite set to its number of elements:

```
cardMap ⟦A⟧ = Nat.card A
```
-/
DefinitionDoc cardMap as "cardMap" in "Quotient"

Statement cardMap : Quotient isoSetoid → ℕ := by
  Hint "[Hint q4cnt] Counting elements does not care which finite set you picked out of a
    class: equivalent sets are precisely those between which there is a bijection, and a
    bijection preserves the number of elements. So `Nat.card` descends to the quotient."
  Hint (hidden := true) "[Hint q4lift] `Quotient.lift` builds the map for you. Feed it
    `fun A : FiniteSets ↦ Nat.card A` and it will ask you for the missing respect proof."
  apply Quotient.lift (fun A : FiniteSets ↦ Nat.card A)
  Hint "[Hint q4resp] What is left is exactly that respect condition: equivalent sets have the
    same number of elements."
  intro A B h
  Hint (hidden := true) "[Hint q4cardeq] `{h}` gives you a bijection, and `Finite.card_eq`
    turns it into the equality of the two numbers."
  apply Finite.card_eq.mpr h

NewDefinition cardMap

TheoremTab "Quotient"
