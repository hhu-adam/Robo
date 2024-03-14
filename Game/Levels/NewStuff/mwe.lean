import Mathlib

namespace Test.Subspaces

variable {V k : Type} [Field k] [AddCommGroup V] [Module k V]

variable (U₁ U₂ : Submodule k V)



example (g : U₁.carrier ⊆ U₂.carrier ∨ U₂.carrier ⊆ U₁.carrier)
    : Submodule k V where
  carrier := U₁.carrier ∪ U₂.carrier
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

example :
    (∃ (W : Submodule k V), W.carrier = U₁.carrier ∪ U₂.carrier) ↔
    U₁.carrier ⊆ U₂.carrier ∨ U₂.carrier ⊆ U₁.carrier := by
  constructor
  · intro h
    sorry
  · intro h
    use U₁ ⊔ U₂
    calc (U₁ ⊔ U₂).carrier
    _ = U₁.carrier ∪ U₂.carrier := sorry




#check U₁.carrier ∪ U₂.carrier

#check Submodule.inclusion

set_option trace.Meta.synthInstance true in

#check U₁ ⊔ U₂

#check Submodule









open CategoryTheory

#check Submodule
#check FullSubcategory

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (U W : Submodule k V)

/-
starting from V and U and W construct a new vector space
V' := U ⊕ W
-/




#synth Sup (Submodule k V)
#check SemilatticeSup.toSup
#synth SemilatticeSup (Submodule k V)

#check Submodule.completeLattice

example : U ⊔ W = V ↔ U ≤ W ∨ W ≤ U := sorry

example (h : U ≤ W ) : U →ₗ[k] W := Submodule.inclusion h




-- Sina


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
example (V' : Type) (V' : Submodule k V)  : U.carrier ∪ W.carrier = V'.carrier ↔ U.carrier ⊆ W.carrier ∨ W.carrier ⊆ U.carrier := sorry

/- 4.
3 -> 4 use Submodule.inclusion
-/
example (V' : Type) (V' : Submodule k V) : U.carrier ∪ W.carrier = V'.carrier ↔ U ≤ W ∨ W ≤ U := sorry

variable {V k : Type} [Field k] [AddCommGroup V] [Module k V]

variable (U₁ U₂ : Submodule k V)

example :
    ∃ (V : Submodule k V), V.carrier = U₁.carrier ∪ U₂.carrier ↔
    U₁.carrier ⊆ U₂.carrier ∨ U₂.carrier ⊆ U₁.carrier := by
  sorry

/- 5.
Extending from binary union to arbitrary union:
induction might be helpful.
-/

end Test.Subspaces



namespace Test

variable (n : ℕ)
example : FiniteDimensional ℚ (Fin n → ℚ) := by
  constructor
  unfold Submodule.FG
  let S := Basis.ofVectorSpace ℚ (Fin n → ℚ) |>.repr

  sorry

-- set_option pp.all true

-- variable (other : Module ℚ ℝ)

#check 1 • 2

#synth SMul ℚ ℝ

#check Rat.num_den
#check Rat.divInt_mul_divInt

example : n /. m = n * (1 /. m) := by

  sorry

#synth Module ℚ ℝ

noncomputable
abbrev RQ := (NormedSpace.toModule : Module ℚ ℝ)

example (a : ℚ) (b : ℝ) : a • b = RQ.smul a b := rfl

set_option trace.Meta.synthInstance true in

example (q : ℤ) (r : ℝ) : q * r = q * r := by
  have y : (q : ℚ) • r = q * r := rfl
  calc  q * r
  _ = (q : ℚ) • r := sorry
  _ = q * r := y


open Rat
example (other: Module ℚ ℝ) : ∀ (r : ℚ) (y : ℝ), other.smul r y = r * y := by
  intro r y
  calc other.smul r y
  _ = other.smul (r.num /. r.den) y                   := by rw [num_den]
  _ = other.smul ((1 * r.num) /. (r.den * 1)) y      := by simp
  _ = other.smul ((1 /. r.den) * (r.num /. 1)) y      := by rw [divInt_mul_divInt] <;> simp [den_nz]
  _ = other.smul ((1 /. r.den) * r.num) y             := by simp [coe_int_eq_divInt]
  _ = other.smul (1 /. r.den) (other.smul (r.num) y)  := other.mul_smul (1 /. r.den) r.num y
  _ = other.smul (1 /. r.den) (RQ.smul r.num y)       := sorry -- this is probably some induction argument on ℤ.
  _ = RQ.smul (1 /. r.den) (RQ.smul r.num y)          := sorry -- this I forgot what the argument was…
  _ = RQ.smul ((1 /. r.den) * r.num) y                := RQ.mul_smul _ _ y |>.symm
  _ = RQ.smul ((1 /. r.den) * (r.num /. 1)) y         := by simp [coe_int_eq_divInt]
  _ = RQ.smul ((1 * r.num) /. (r.den * 1)) y          := by rw [divInt_mul_divInt] <;> simp [den_nz]
  _ = RQ.smul (r.num /. r.den) y                      := by simp
  _ = RQ.smul r y                                     := by rw [num_den]
  _ = r * y                                           := rfl




end Test



namespace Test
end Test
