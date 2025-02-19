import Game.Metadata


World "Samarkand"
Level 3

Title "" -- "Range of Surjection"


Introduction
"
The range of a function is the set of all outputs.

In this level you show that a function is surjective if and only if the range of
the function is equal to the universal subset of the codomain. For `f : A → B`,
the range of `f` is defined as

```
range f : Set B := {b | ∃ a, f a = b}
```

"

open Function Set

Statement {A B : Type} {f : A → B} : Surjective f ↔ range f = univ := by
  Branch
    exact eq_univ_iff_forall.symm
  constructor
  · intro hf
    Hint "**Du**: Wie zeigt man denn schon wieder Gleichheit von Mengen?"
    ext b
    Branch
      tauto
    constructor
    · tauto
    · intro
      Hint "**Robo**: Ich habe ein relevantes Resultat gefunden: `mem_range`.
      Such das mal in denem Inventar!
      "
      rw [mem_range] -- not necessary but desirable for the user.
      apply hf
  · intro h
    intro b
    Branch
      simpa [← h] using mem_univ b
    rw [← mem_range]
    rw [h]
    tauto

NewDefinition Set.range
NewTheorem Set.mem_range
