import Game.Metadata
import Game.Metadata.StructInstWithHoles

World "Quotient"
Level 2

Title "Quotient"

Introduction
"
Given a setoid structure `s` on `A` and an element `a : A` the equivalence class of `a`
is the set of all elements of `A` that are congruent to `a`, namely `{x : A | s.Rel x a}`.

We say a function `f : A → B` is equifibred if for any two elements `x` and `y` of `B` the
preimages of `x` and `y` are equivlanet.

In this level you show that the equivalence classes of an equifibred function are all equivalent.

"

open Function Set Setoid

section
-- The following lemma is useful: it says that the elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f.
#check ker_iff_mem_preimage
end


Statement equiv_classes_of_equifibred (f : A → B)
    (e : ∀ b b' : B, (f ⁻¹' {b}) ≃ (f ⁻¹' {b'})) :
    ∀ u v, u ∈ (ker f).classes → v ∈ (ker f).classes → u ≃ v := by
  intro u v hu hv
  refine {?..!}
  · sorry
  · sorry
  · sorry
  · sorry
