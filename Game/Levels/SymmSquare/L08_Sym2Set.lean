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

open Function Sym Finset Set Quotient

-- PRd to mathlib #13302 -- declined (?)
@[simp]
theorem card_pair_eq_one_or_two {A : Type*} [DecidableEq A] (a b : A) :
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

theorem helper {A : Type*} [DecidableEq A] {a₁ a₂ b₁ b₂ : A} (h₁ : a₁ ≠ a₂) (h₂ : b₁ ≠ b₂)
    (h : ({a₁, a₂} : Finset A) = {b₁, b₂}) : (a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁) := by
  -- I'm going mad xD
  rw [Finset.ext_iff] at h
  have q₁ := (h a₁).mp (Finset.mem_insert_self _ _)
  have q₂ := (h a₂).mp
  rw [Finset.pair_comm] at q₂
  replace q₂ := q₂ <| Finset.mem_insert_self a₂ {a₁}
  rw [Finset.mem_insert, Finset.mem_singleton] at q₁ q₂
  aesop

theorem card_eq_one_or_two {A : Type*} [DecidableEq A] (S : Finset A) :
    S.card = 1 ∨ S.card = 2 ↔ ∃ a b, S = {a,b} := by
  constructor
  · intro h
    rcases h with h | h
    · rw [card_eq_one] at h
      rcases h with ⟨s, hs⟩
      use s, s
      simp
      assumption
    · rw [card_eq_two] at h
      rcases h with ⟨s, t, _h₁, h₂⟩
      use s, t
  · rintro ⟨a, b, rfl⟩
    simp

Statement {A : Type*} [DecidableEq A] : (Sym2 A) ≃ { S : Finset A // S.card = 1} ⊕ { S : Finset A // S.card = 2 } := by
  let f : Sym2 A → { S : Finset A // S.card = 1 } ⊕ { S : Finset A // S.card = 2 } :=
    Quot.lift (
      fun ⟨a, b⟩ => if h : a = b then .inl ⟨{a}, rfl⟩ else .inr ⟨{a, b}, card_pair h⟩) (by
        -- this would be `aesop` but it's too slow so I replaced it while working on it.
        intro a b h
        rw [Sym2.rel_iff'] at h
        rcases h with h | h
        dsimp only
        · rw [h]
        · rw [h]
          dsimp only [Prod.fst_swap, Prod.snd_swap]
          by_cases h₂ : b.1 = b.2
          · rw [h₂]
          · simp only [h₂, ↓reduceDite]
            have h₃: ¬ (b.2 = b.1) := fun x => h₂ x.symm
            simp only [h₃, ↓reduceDite]
            simp_all only [Sum.inr.injEq, Subtype.mk.injEq]
            rw [Finset.pair_comm])
  refine' Equiv.ofBijective f _
  constructor
  · intro b c hbc
    simp [f] at hbc
    clear f
    obtain ⟨b', hb⟩ := Quot.exists_rep b
    obtain ⟨c', hc⟩ := Quot.exists_rep c
    rw [← hb, ← hc ] at hbc ⊢
    simp at *
    by_cases h : b'.1 = b'.2
    · by_cases h₂ :c'.1 = c'.2
      · simp [h, h₂] at hbc
        aesop
      · simp [h, h₂] at hbc
    · simp [h, reduceDite] at hbc
      by_cases h₂ :c'.1 = c'.2
      · simp [h, h₂] at hbc -- , Subtype.mk.injEq
      · simp [h, h₂, ↓reduceDite] at hbc
        apply helper h h₂ at hbc
        rw [Prod.eq_iff_fst_eq_snd_eq, Prod.eq_iff_fst_eq_snd_eq]
        rw [Prod.fst_swap, Prod.snd_swap]
        assumption
  · intro y
    rcases y with y | y
    · have y₂ := y.2
      rw [card_eq_one] at y₂
      choose a ha using y₂
      use Quot.mk _ (a, a)
      simp [f]
      apply Subtype.val_injective
      exact ha.symm
    · have y₂ := y.2
      rw [card_eq_two] at y₂
      choose a b hab₁ hab₂ using y₂
      use Quot.mk _ (a, b)
      simp [f]
      simp only [hab₁, ↓reduceDite, Sum.inr.injEq]
      apply Subtype.val_injective
      exact hab₂.symm

/-- Multisets cannot have a head/first element. -/
theorem headless  : ¬ ∃ f : Multiset ℕ → ℕ, ∀ l : List ℕ, ∀ (h : l ≠ []), f l = l.head h := by
  push_neg
  intro f
  by_cases h : f [0, 1] = 0
  · use [1, 0], List.cons_ne_nil _ _
    have h₀ : ([0, 1] : Multiset ℕ) = ↑[1, 0] := by
      apply Multiset.pair_comm
    rw [← h₀, h]
    simp only [List.head_cons, ne_eq, zero_ne_one, not_false_eq_true]
  · use [0, 1], List.cons_ne_nil _ _
    contrapose h
    simp at *
    assumption
