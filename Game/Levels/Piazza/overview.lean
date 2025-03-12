import Mathlib

/-
Story am Ende:  Kinder klauen bunte Dinger aus den Körben, dann legen sie sie wieder zurück.
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

/- Piazza L08: univ -/
namespace Set
example {T : Type} (A B : Set T) :
  univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  ext i
  simp
  tauto
end Set

/- Piazza L07a -/
namespace Set
example :  { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  ext
  simp

/- Piazza L07b -/
example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  ext n
  simp
  by_cases h : Even n
  · left
    assumption
  · right
    assumption


/- Piazza L03 -/
/-
example {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  simp [Set.subset_def] at *
  tauto
-/
-- direct solution seems better:
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

/- Piazza L04: DELETE  -/
/-
example : ({2, 7} : Set ℕ) ⊆ {2, 3, 7, 9} := by
  -- ! can also be solved directly with simp !
  -- TODO: Better exercise about `intro`     ?
  intro x
  simp
  tauto
-/

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


/- Piazza L11* -/
example : {2, 7} ⊆ {2} ∪ Icc 0 10 ∩ { n : ℕ | Odd n} := by
  intro x
  intro h
  simp at *
  obtain h | h := h
  · tauto
  · simp [h]
    decide


/- Piazza L06:  Set.empty; not needed anymore; DELETE -/
/-
theorem Robo.Set.eq_empty_iff_forall_not_mem {A : Type} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  constructor
  · intro h
    rw [h]
    tauto
  · intro h
    ext i
    tauto
-/

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
