import Mathlib


section ExDisjoint
variable {S : Type} (A B : Set S)
--#check Sum A B
open Function

def can : ↑A ⊕ ↑B → ↑(A ∪ B) := fun x ↦
 match x with
 | .inl a => ⟨a,by simp⟩
 | .inr b => ⟨b,by simp⟩

lemma can_surjective : Surjective (can A B):= by
  intro s
  have : s ∈ A ∪ B := Subtype.coe_prop s

example (a : (A : Type)) : 1=1 := by --a ∈ (A : Set S) := by exact?
  have : a ∈ (A : Set S) := by exact?
  rw [coeSubtype ]
end ExDisjoint


open Function
#check Fintype
variable (A : Type) [Fintype A]
#check Fintype.card A

variable (B : Type) [Finite B]
#check Set.ncard (Set.univ : Set B)


noncomputable example {A : Type} [Fintype A] (S : Set A) : Fintype S := by
  exact Fintype.ofFinite ↑S

noncomputable example {A : Type} [Finite A] (S : Set A) : Finite S := by
  exact Subtype.finite

#check Set.range
#check Finset.range

open Set
lemma subset_eq_if_ncard_eq {M : Type} {A B : Set M} [hA : Finite A] [hB : Finite B] (h : A ⊆ B):
  A = B ↔ ncard A = ncard B := by
  constructor
  · intro h_eq
    rw [h_eq]
  · intro h_ncard
    have hu : ncard B ≤ ncard A := by linarith
    rw [← Set.subset_iff_eq_of_ncard_le hu hB]
    assumption

/-lemma subset_eq_if_ncard_eq {A : Type} [Finite A] (S : Set A) :
  S = univ ↔ ncard S = ncard (univ : Set A) := by
  constructor
  · intro h
    rw [h]
  · intro h
    have hu : ncard (univ : Set A) ≤ ncard S := by linarith
    rw [← Set.subset_iff_eq_of_ncard_le hu Subtype.finite]
    tauto
    -/

lemma fin_surj_range {A B : Type} [Finite A] [Finite B] (f : A → B) :
  Surjective f ↔ ncard (range f) = ncard (univ : Set B) := by
  have : range f ⊆ (univ : Set B) := by tauto
  rw [← subset_eq_if_ncard_eq this]
  exact Iff.symm Set.range_iff_surjective

/-lemma fin_bij {A B : Type} [Fintype A] [Fintype B] (h : Fintype.card A = Fintype.card B) (f : A → B) :
  Injective f → Surjective f := by
  sorry
-/
