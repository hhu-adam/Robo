import Mathlib

/- Piazza L01 -/
namespace Set
example : 3/2  ∈ ({3/2, 16/9, 4/7} : Set ℚ) := by
  tauto
end Set
/-
namespace Finset
example : 1 ∈ ({1, 6, 4} : Finset ℕ) := by
  tauto
end Finset
-/

/- Piazza 02: `simp` -/
example : 9 ∈ {n : ℕ | Odd n} := by
  simp
  decide


/- Piazza L03: `ext` -/
namespace Set
example {T : Type} (A B C : Set T) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp -- simp only [mem_inter_iff, mem_union]
  tauto
end Set
/-
namespace Finset
example (A B C : Finset ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp -- simp only [mem_inter_iff, mem_union]
  tauto
end Finset
-/

/- Piazza L04: `univ`, `eq_univ_iff_forall` -/
namespace Set
example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  rw [eq_univ_iff_forall]
  simp
  intro x
  generalize h : (Even x) = A
  tauto
end Set

/- Piazza L05: `empty`, `eq_empty_iff_forall_not_mem` -/
namespace Set
example :  { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  simp

/- Piazza L06 -/
namespace Set
example {T : Type} (A B : Set T) :
  univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  ext i
  simp
  tauto
end Set

/- Piazza L07: used in CANTOR -/
namespace Set
theorem Robo.Set.Subset.antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext i
    tauto
end Set
/-
namespace Finset
theorem Robo.Set.Subset.antisymm_iff {α : Type} {A B : Finset α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext i
    tauto
end Finset
-/

/- Piazza 08: `subset_iff` -/
/- following theorem exists in Mathlib and is used in Luna -/
theorem Robo.Finset.subset_iff {A : Type} {s₁ s₂ : Finset A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

/- The `Set`-version of the theorem is currently included via
   Game/Metadata/MathlibPreview.lean
   Jon has a Mathlib PR with this theorem.
-/
theorem Robo.Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

/- Piazza L09 -/
-- direct solution:
namespace Set
example {T : Type} {A B C : Set T} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  -- rw [subset_iff] at * -- optional
  intro a ha
  apply h₁ at ha
  apply h₂ at ha
  assumption
end Set
/-
namespace Finset
example {A B C : Finset ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  intro a ha
  apply h₁ at ha
  apply h₂ at ha
  assumption
end Finset
-/

/- Piazza L11* -/
example : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  intro x
  intro h
  simp at *
  obtain h | h := h
  · tauto -- or  left, assumption
  · right
    rw [h]
    decide

theorem Robo.Set.eq_univ_iff_forall {A : Type} {s : Set A} :
  s = univ ↔ ∀ (x : A), x ∈ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext a
    tauto


/- Piazza N01 -/
namespace Finset
example (A : Finset ℕ) (a : ℕ) : Finset.erase A a = A \ {a} := by
  ext
  simp
  tauto

/- Piazza N02 -/
example (A : Finset ℕ) (a : ℕ) : insert a A = A ∪ {a} := by
  ext
  simp
  tauto

/- Piazza N03 -/
theorem Robo.Finset.insert_erase {A : Type} [DecidableEq A] {s : Finset A} {a : A} (h : a ∈ s) :
  insert a (Finset.erase s a) = s := by
  ext b
  simp
  --
  by_cases heq : b = a
  · rw [heq]
    tauto
  · simp [heq]
  /-
  constructor
  · intro h
    obtain h₁ | ⟨ h₂, h₃ ⟩ := h
    rw [← h₁] at h
    assumption
    assumption
  · intro hb
    by_cases heq: b = a
    left
    assumption
    right
    constructor
    assumption
    assumption
  -/
end Finset


/- obsolete levels -/

/- Piazza L06:  proof of `eq_empty_iff_forall_not_mem` -/
/-
theorem Robo.Set.eq_empty_iff_forall_not_mem {A : Type} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext a
    tauto
-/

/- Piazza O09: complement -/
/-
namespace Set
example (A B C : Set ℕ) :
    (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  ext i
  simp
  tauto
end Set
-/
