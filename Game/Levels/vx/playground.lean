import Mathlib

open Function
#check Fintype
variable (A : Type) [Fintype A]
#check Fintype.card A

variable (B : Type) [Finite B]
#check Set.ncard (Set.univ : Set B)


lemma fin_bij {A B : Type} [Fintype A] [Fintype B] (h : Fintype.card A = Fintype.card B) (f : A → B) :
  Injective f → Surjective f := by
  sorry

noncomputable example {A : Type} [Fintype A] (S : Set A) : Fintype S := by
  exact Fintype.ofFinite ↑S

noncomputable example {A : Type} [Finite A] (S : Set A) : Finite S := by
  exact Subtype.finite

#check Set.range
#check Finset.range

open Set
lemma eq_if_same_card {A : Type} [Finite A] (S : Set A) :
  S = univ ↔ ncard S = ncard (univ : Set A) := by
  sorry

lemma fin_surj_range {A B : Type} [Finite A] [Finite B] (f : A → B) :
  Surjective f ↔ ncard (range f) = ncard (univ : Set B) := by
  rw [← eq_if_same_card]
  exact Iff.symm Set.range_iff_surjective
