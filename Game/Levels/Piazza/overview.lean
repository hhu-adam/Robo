import Mathlib

/-
Story am Ende:  Kinder klauen bunte Dinger aus den Körben, dann legen sie sie wieder zurück.

Icc *not* anymore used here in Piazza, as Luna will depend on Piazza.
-/

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

/- Piazza L10 -/
-- simp NEEDS TO BE INTRODUCED HERE!
example : 9 ∈ {n : ℕ | Odd n} := by
  simp
  decide


/- Piazza L02 -/
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

/- Piazza L07a: univ -/
namespace Set
example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  rw [eq_univ_iff_forall]
  simp
  intro x
  -- from here, there are two alternatives; one is:
  generalize h : (Even x) = A
  tauto

example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  ext n
  simp
  -- here, we are in the same state as with the previous branch;
  -- alternative way to proceed is:
  by_cases h : Even n
  · left
    assumption
  · right
    assumption
end Set

/- Piazza L07b: empty -/
namespace Set
-- first mention `eq_empty_iff_forall_not_mem` as a strategy
-- to “unfold” definition of emptyset
example :  { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  simp

example :  { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  ext
  simp

/- Piazza L08: univ -/
namespace Set
-- first mention `eq_univ_iff_forall` as a strategy
-- to “unfold” definition of `univ`
example {T : Type} (A B : Set T) :
  univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  ext i
  simp
  tauto
end Set

/- Piazza L05: used in CANTOR -/
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


/- Piazza L03 -/
-- direct solution:
namespace Set
example {T : Type} {A B C : Set T} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
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

/- Piazza NEW -/
/- following theorem exists in Mathlib and is used in Luna -/
theorem Robo.Finset.subset_iff {A : Type} {s₁ s₂ : Finset A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

/- following theorem should be shown here, because it will be useful;
   Jon has a Mathlib PR with this theorem.
   TODO:  update level when PR becomes available.
-/
theorem Robo.Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

/- Piazza L03b -/
-- solution to exercise above with `subset_iff`, the Finset-version of which is used in BOSS level of LUNA
/-
example {A B C : Finset ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  simp [Finset.subset_iff] at *
  tauto
-/
example {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  simp [Set.subset_def] at *
  tauto

/- Piazza L04: DELETE  -/
/-
example : ({2, 7} : Set ℕ) ⊆ {2, 3, 7, 9} := by
  -- ! can also be solved directly with simp !
  -- TODO: Better exercise about `intro`     ?
  intro x
  simp
  tauto
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

/- Piazza L06:  needed in SAMARKAND -/
theorem Robo.Set.eq_empty_iff_forall_not_mem {A : Type} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext a
    tauto

theorem Robo.Set.eq_univ_iff_forall {A : Type} {s : Set A} :
  s = univ ↔ ∀ (x : A), x ∈ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext a
    tauto


/- Piazza L07:  sehr künstliche Aufgabe, um Set.univ einzuführen; DELETE -/
/-
namespace Set
example (h : (univ : Set ℕ) ⊆ ∅) : (univ : Set ℕ) = ∅ := by
  tauto
end Set

namespace Finset
example (n : ℕ) (h : (univ : Finset (Fin n)) ⊆ ∅) : (univ : Finset (Fin n)) = ∅ := by
  ext -- only needed in this version
  tauto
end Finset
-/


/- Piazza L09: DELETE -/
/-
namespace Set
example (A B C : Set ℕ) :
    (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  ext i
  simp
  tauto
end Set
-/


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
