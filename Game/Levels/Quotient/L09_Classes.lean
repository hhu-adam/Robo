import Game.Metadata
import Game.Levels.Quotient.L08_Classes

World "Quotient"
Level 9

Title "Classes"

Introduction
"
Recall from the previuos level that given a setoid structure `s` on `A` and an element `a : A`
the equivalence class of `a` is the set of all elements of `A` that are congruent to `a`, namely `{x : A | s.Rel x a}`.

In this level we show that the set of equivalence classes of `A` under the relation `s` is in
bijection with the quotient `Quotient s`.

"

open Function Set Setoid

Statement bijective_of_quotient_to_classes (s : Setoid A) :
    ∃ f : Quotient s → s.classes, Bijective f := by
  let f : A → s.classes := fun a ↦ ⟨{ x : A | s.Rel x a }, Setoid.mem_classes s a⟩
  have f_respects_relation : ∀ a b, a ≈ b → f a = f b := by
    intro a b h
    rw [Subtype.mk.injEq]
    apply (rel_iff_eq_classes a b).mp h
  use Quotient.lift f f_respects_relation
  constructor
  · intro qa qb heq
    -- obtain ⟨a⟩ := qa
    -- obtain ⟨b⟩ := qb
    obtain ⟨a, ha⟩ := Quotient.exists_rep qa
    obtain ⟨b, hb⟩ := Quotient.exists_rep qb
    rw [← ha, ← hb] at heq
    simp [Quotient.lift_mk] at heq
    rw [← ha, ← hb]
    apply Quotient.sound
    simp [f] at heq
    exact (rel_iff_eq_classes a b).mpr heq
  · rw [Quot.surjective_lift]
    intro ⟨cl, a, hcl⟩
    use a
    apply Subtype.ext
    dsimp
    symm
    assumption


NewTheorem Quotient.lift_mk
TheoremTab "Quotient"
