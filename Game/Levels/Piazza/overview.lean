import Mathlib


/- TODO
   A: introduce  Finset.Icc_subset_Icc_iff,
      needed for BABYLON exercise introucing sub_subset;
      see L03a

   B: another preparation for BABYLON, sub_sumset exercise;
      see L08a

   C: Set.insert, Set.erase & lemma Set.insert_erase
      TODO!
-/

open Set Finset
/- Piazza L01 -/
example : 1 ∈ ({1, 6, 4} : Set ℕ) := by
  tauto

example : 1 ∈ ({1, 6, 4} : Finset ℕ) := by
  tauto

/- Piazza L02 -/
example (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp -- simp only [mem_inter_iff, mem_union]
  tauto

example (A B C : Finset ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp -- simp only [mem_inter_iff, mem_union]
  tauto

/- Piazza L03 -/
example {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  simp [Set.subset_def] at *
  tauto

/- Piazza L03a NEW: Icc, Icc_subset_Icc_iff
   This is about Finsets, so does not quite belong here.
   But this is the version needed in BABYLON,
   and it's much easier to solve because omega is more powerful than linarith -/
theorem Robo.Finset.Icc_subset_Icc_iff (a₁ b₁ a₂ b₂ : ℕ) (h₁ : a₁ ≤ b₁) :
  Finset.Icc a₁ b₁ ⊆ Finset.Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  -- unfold Icc -- optional
  simp [Finset.subset_iff]
  -- omega -- still fails here
  constructor
  · -- omega -- still fails here
    intro h
    have h' := h
    specialize h h₁
    have : a₁ ≤ a₁ := by rfl
    specialize h' this
    omega
  · omega

/- Piazza L04 -/
example : ({2, 7} : Set ℕ) ⊆ {2, 3, 7, 9} := by
  -- ! can also be solved directly with simp !
  -- TODO: Better exercise about `intro`     ?
  intro x
  simp
  tauto


/- Piazza L05 -/
theorem Robo.Set.Subset.antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext i
    tauto

/- Piazza L06 -/
theorem Robo.Set.eq_empty_iff_forall_not_mem {A : Type} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext i
    tauto

/- Piazza L07:  sehr künstliche Aufgabe, um Set.univ einzuführen -/
example (h : (univ : Set ℕ) ⊆ ∅) : (univ : Set ℕ) = ∅ := by
  tauto

/- Piazza L08: könnte schon nach L02 kommen; vielleicht ganz überflüssig -/
example (A B : Set ℕ) :
  univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  ext i
  simp
  tauto

/- L08a NEW:  Preparation for exercise in BABYLON
   Again, this is for Finset,
   but again this makes it significantly simpler, and is all that is needed later.
   -/
example (n x : ℕ) (h : 3 ≤ n): x ∈ Icc 0 n \ Icc 3 n → x = 0 ∨ x = 1 ∨ x = 2 := by
  intro h
  simp at h
  omega

-- variation, still in ℕ:
-- more natural statement but less revelant for BABYLON
example (l m n : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : Icc l n \ Icc m n  ⊆ Icc l m := by
  simp [subset_def]
  omega

-- variation, now in ℝ
-- most natural statement, but much more difficult, and not at all revelant for BABYLON
example (l m n : ℝ) (h₁ : l ≤ m) (h₂ : m ≤ n) : Icc l n \ Icc m n  ⊆ Icc l m := by
  simp [subset_def]
  intro x hlx hxn h
  rw [imp_iff_or_not] at h
  obtain hx | hx := h
  · linarith
  · -- linarith (config := {splitNe := true, splitHypotheses := true}) -- fails here!
    constructor
    · linarith
    · linarith

/- NEW -/
example (A : Set ℕ) (a : ℕ) : Finset.erase a A = A \ {a} := by
      simp

/- Piazza L09: könnte schon nach L02 kommen; vielleicht ganz überflüssig -/
example (A B C : Set ℕ) :
    (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  ext i
  simp
  tauto

/- Piazza L10 -/
example : 9 ∈ {n : ℕ | Odd n} := by
  simp
  decide

/- Piazza L11 -/
example : {2, 7} ⊆ {n : ℕ | n = 2 ∨ (n ≤ 10 ∧ Odd n)} := by
  intro x
  intro h
  simp at *
  obtain h | h := h
  · tauto
  · simp [h]
    decide
