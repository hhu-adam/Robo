import Game.Metadata

import Game.Levels.Quotient.L14_KernelRespect

World "Quotient"
Level 15

Title "Bijection"

Introduction
"
Use the following:
Given a map `f : A → B`, the theorem `ker_lift_injective` says that the canonical lift map from
`A/ker f → B` is injective.

"

open Function Set Setoid Quotient

-- #check Setoid.ker_lift_injective

Statement {f : A → B} :
    have respects_ker_rel : ∀ (a b : A), (ker f).Rel a b → f a = f b := by
      intro a b h
      assumption
    Injective (Quotient.lift (s:= ker f) f respects_ker_rel) := by
  intro x y h
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  obtain ⟨b, hb⟩ := Quotient.exists_rep y
  Branch
    rw [←ha, ←hb] at h
    simp [Quotient.lift_mk] at h
    rw [← ha, ← hb]
    simp
    assumption
  simp [←ha, ←hb] at *
  assumption


-- Remark: another way to prove the injectivity and surjectivity of the quotient lift is to use
--the cancellation properties. This would still use `ker_lift_injective`
