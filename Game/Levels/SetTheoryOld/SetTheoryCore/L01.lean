import Game.Metadata

World "SetTheory"
Level 1

Title "Mengen"

Introduction
"

"

-- Given a type `X`, a set `s` of `X` is a selection of elements of `X`. In Lean we write `s : Set X`.

-- For example the set of natural numbers, selecting only `1`, `4` and `6`, can be written as `({1,4,6} : Set ℕ)`.

-- The main relation between elements of `X` and sets of `X` is the membership relation `∈`. We write `x ∈ s` to say that `x` is in `s`.

open Set

Statement : 1 ∈ ({1,4,6} : Set ℕ) := by
  tauto

-- example : 1 ∈ ({1,4,6} : Set ℕ) := by
--   simp only [mem_insert_iff, OfNat.one_ne_ofNat, mem_singleton_iff, or_self, or_false]


DefinitionDoc Set.mem as "∈"

NewDefinition Set.mem
TheoremTab "Set"

Conclusion "**Mengea**: Ja das stimmt schon. Dann wünsche ich euch viel Erfolg auf eurer Reise!"
