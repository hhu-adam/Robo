import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.FibreSetoid


World "Quotient"
Level 2

Title "Quotient"

Introduction
"
For a congruence `r` on a type `A`, the quotient type `Quotient r` is the type of
elements of `A` modulo `r`.  A mathematically common notation for `Quotient r` is `A / r`.
We can think of `Quotient r` as the collection of equivalence classes `⟦a⟧` of elements `a : A` modulo `r`.
The function `Quotient.mk : A → Quotient r` maps an element `a : A` to its equivalence class `⟦a⟧`.
If elements `a b : A` are congruent, then `⟦a⟧ = ⟦b⟧`. This fact is witnessed
by `Quotient.sound`.

The simplest induction principle `Quotient.ind` for the quotient type states that a property of elements of `Quotient r` can be proved by showing that it holds for all congruence classes `⟦a⟧`. In other words, if a property `P` holds for all congruence classes `⟦a⟧`, then `P` holds for all elements of `Quotient r`.

The crucial universal property of `Quotient r` is the following statement:
If `f : A → B` is any function that
respects the congruence `r` in the sense that for every `x y : A`,
`r x y` implies `f x = f y`, then `f` uniquely lifts to a function `Quotient.lift f : Quotient r → B`
defined on each equivalence class `⟦a⟧` by `Quotient.lift f ⟦a⟧ = f a`.

In this level you show that the function `Quotient.mk : A → Quotient fiber_setoid` is surjective.

"

open Function

Statement {f : A → B} : Surjective (Quotient.mk <| fibre_setoid <| f) := by
  intro b
  induction b using Quotient.ind
  use a
