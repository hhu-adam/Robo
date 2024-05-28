import Game.Metadata
import Game.Levels.SymmSquare.L02_Sym2

World "Symmetric Square"
Level 8

Title "Classifying Symmetric Functions"

Introduction
"

In this level you show that there is a 1-1 correspondence between unordered pairs and subsets
with 1 or 2 elements.
"

open Function Sym Finset

-- PR to mathlib #13302
@[simp]
theorem card_one_or_two {A : Type*} [DecidableEq A] (a b : A) :
    ({a,b} : Finset A).card = 1 ∨ ({a,b} : Finset A).card = 2 := by
  simp [card_insert_eq_ite]
  tauto

-- @[simp]
-- theorem card_one_or_two {A : Type*} [DecidableEq A] (a b : A) :
--     ({a,b} : Finset A).card = 1 ∨ ({a,b} : Finset A).card = 2 := by
--   by_cases h : a = b
--   · rw [h]
--     left
--     simp only [insert_eq_of_mem, mem_singleton, card_singleton]
--   · right
--     apply card_pair h

#check Equiv.trans
#check card_eq_one
#check card_eq_two

theorem card_eq_one_or_two {A : Type*} [DecidableEq A] (S : Finset A) :
    S.card = 1 ∨ S.card = 2 ↔ ∃ a b, S = {a,b} := by
  constructor
  · intro h
    cases h
    · sorry
    · sorry
  · rintro ⟨a, b, rfl⟩
    simp

Statement {A : Type*} [DecidableEq A] : (Sym2 A) ≃ { S : Finset A | S.card = 1 ∨ S.card = 2 } := by
  fconstructor
  · exact Quot.lift (fun ⟨a, b⟩ => ⟨{a,b}, card_one_or_two a b ⟩) (by aesop)
  · exact fun ⟨S, h⟩ => sorry
  · sorry
  · sorry
