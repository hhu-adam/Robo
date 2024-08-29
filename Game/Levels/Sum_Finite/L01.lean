import Game.Metadata

import Mathlib.Data.Finset.Basic

World "Finite"
Level 1

Title "Finite sets are sets."

Introduction
"
There is a coercion `toSet`


"


open Finset

-- example {X : Type*} [DecidableEq X] {A B C : Finset X} :
--   A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
-- by
--   sorry

def foo (A : Finset ℕ) : Set ℕ :=
  A -- this is a coercion from `Finset` to `Set`

#check Multiset

section
variable (l : Multiset ℕ)
-- #check l.head -- a multiset cannot have a `head`.


#check List.head

set_option trace.Meta.synthInstance.instances true in
theorem headless  : ¬ ∃ f : Multiset ℕ → ℕ, ∀ l : List ℕ, ∀ (h : l ≠ []), f l = l.head h := by
  sorry


end

#print foo


section

variable {X : Type} (s : Set X)


end


#check ({2} : Finset ℕ)



example {A B C : Finset ℕ} :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by
  ext x
  simp only [mem_inter, mem_union]
  tauto
