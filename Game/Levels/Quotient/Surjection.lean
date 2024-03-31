import Game.Metadata
import Game.Metadata.StructInstWithHoles

World "Quotient"
Level 3

Title "Quotient"

Introduction
"
For a congruence `r` on a type `A`, the quotient type `Quotient r` is the type of
elements of `A` modulo `r`.  A mathematically common notation for `Quotient r` is `A / r`.

There is a function `Quotient.mk : A → Quotient r` which maps an element `a : A` to  `⟦a⟧`, a typical element of `Quotient r`.

If elements `a b : A` are congruent, then `⟦a⟧ = ⟦b⟧`. This fact is witnessed
by `Quotient.sound`.

The simplest induction principle `Quotient.ind` for the quotient type states that we can prove a property of elements of `Quotient r` if we can prove that it holds for all typical elements `⟦a⟧`.

In this level you show that the function `Quotient.mk : A → Quotient fiber_setoid` is surjective.

"

open Function Set Setoid

Statement surj_quotient_mk_ker (f : A → B) : Surjective (Quotient.mk <| ker <| f) := by
  intro b
  induction b using Quotient.ind
  use a
