import Mathlib

open CategoryTheory

#check Submodule
#check FullSubcategory


section Q1

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (U W : Submodule k V)

/-
starting from V and U and W construct a new vector space
V' := U ⊕ W
-/


/-
Idea (?): Maybe make a world where we introduce the construction of join/sup of two subspaces.
-/

#synth Sup (Submodule k V)
#check SemilatticeSup.toSup
#synth SemilatticeSup (Submodule k V)

#check Submodule.completeLattice

example : U ⊔ W = V ↔ U ≤ W ∨ W ≤ U := sorry

example (h : U ≤ W ) : U →ₗ[k] W := Submodule.inclusion h





/- 1. -/
example (g : U.carrier ⊆ W.carrier ∨ W.carrier ⊆ U.carrier)
    : Submodule k V where
  carrier := U.carrier ∪ W.carrier
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

/-2. -/
example : U.carrier ∪ W.carrier = ⊤ ↔ U.carrier ⊆ W.carrier ∨ W.carrier ≤ U.carrier := sorry

/- 3. -/
example (V' : Type) (V' : Submodule k V)  : U.carrier ∪ W.carrier = V'.carrier ↔ U.carrier ⊆ W.carrier ∨ W.carrier ⊆ U.carrier := by
  constructor
  · intro h

  · sorry

/- 4.
3 -> 4 use Submodule.inclusion
-/
example (V' : Type) (V' : Submodule k V) : U.carrier ∪ W.carrier = V'.carrier ↔ U ≤ W ∨ W ≤ U := sorry

variable {V k : Type} [Field k] [AddCommGroup V] [Module k V]

variable (U₁ U₂ : Submodule k V)

example :
    (∃ (W : Submodule k V), W.carrier = U₁.carrier ∪ U₂.carrier) ↔
    U₁.carrier ⊆ U₂.carrier ∨ U₂.carrier ⊆ U₁.carrier := by
  constructor
  · sorry
  · intro h
    use U₁ ⊔ U₂
    sorry

/- 5. Final verison ?-/
example :
    (∃ (W : Submodule k V), W.carrier = U₁.carrier ∪ U₂.carrier) ↔
    U₁ ≤ U₂ ∨ U₂ ≤ U₁ := by
  constructor
  · intro h
    sorry
  · intro h
    use U₁ ⊔ U₂
    sorry

/- 6.
Extending from binary union to arbitrary union:
induction might be helpful.
-/

end Q1

section Q2

/- ## Infinite Dim Vector Space ℝ over ℚ -/

/- 1. Show that $ℚ^n$ is a finite dimensional vector space over $ℚ$.
-/

example : FiniteDimensional ℚ (Fin n → ℚ) where --by infer_instance
  out := by
    sorry

/- 2. Show that if $ℝ$ with its standard addition is a vector space over $ℚ$ then the scalar multiplication is given by the standard multiplication of real numbers.

Rephrase (?): once the addition structure on ℝ is given, there is a unique vectors space structure on ℝ over ℚ.
-/

def V := ℝ

#synth AddCommGroup ℝ

instance foo : AddCommGroup V := Real.instAddCommGroupReal

#synth Module ℚ ℝ
#synth Module ℚ V


-- example [Module ℚ V] :



#check Module

example (other : Module ℚ ℝ) : ∀ (r : ℚ) (y : ℝ), other.smul r y = r * y := by
  intro r y
  sorry

#check one_smul


/-
q • r = m/n • r = (n⁻¹ m) • r  = (n)⁻¹ • (m • r) is given b.c.

1. m • r = (r + r + ... + r) is given `add_smul` and `one_smul`
2. for any n : ℤ, n⁻¹ • r = x  ↔ r = n • x = (x + x + ... + x) ↔ x = r/n
-/

end Q2
