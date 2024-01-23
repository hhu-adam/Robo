-- Level name : Überabzählbarkeit von ℝ

import linear_algebra.dimension
import linear_algebra.finite_dimensional
import field_theory.cardinality
import data.real.basic
import data.real.cardinality
import set_theory.cardinal.basic

universe u

-- Tell Lean to use that `V` has finitely many elements, so we can use `‖V‖` below.
-- noncomputable instance V_fintype : fintype V := finite_dimensional.fintype_of_fintype 𝔽ₚ V

local notation `‖` x `‖` := fintype.card x
local notation `dim` := finite_dimensional.finrank  -- or: module.rank 𝔽ₚ V? (they are equal:`finite_dimensional.finrank_eq_dim`)

lemma cardinal_eq_of_finite_basis
  {K V : Type u} {ι : Type u} [field K] [add_comm_group V] [module K V] [fintype ι]
  (h : cardinal.mk K = cardinal.aleph_0) (h2: basis ι K V) :
  cardinal.mk V ≤ cardinal.aleph_0 :=
begin
  rw cardinal.mk_congr (h2.equiv_fun.to_equiv),
  rw ←cardinal.power_def,
  rw h,
  simp only [cardinal.mk_fintype, cardinal.pow_cast_right],
  apply cardinal.power_nat_le,
  refl,
end

/- Lemma
Beweise.
-/
example : ¬finite_dimensional ℚ ℝ :=
begin
  introI h,   -- Instead of by_contradiction,

  -- Widerspruch: Wir wissen dass ℝ nicht countable ist.
  apply cardinal.not_countable_real,

  rw ←cardinal.le_aleph_0_iff_set_countable,
  rw cardinal.mk_univ,

  set B := basis.of_vector_space ℚ ℝ,

  --have qq := dim_eq_card_basis B,

  convert cardinal_eq_of_finite_basis _ B,
  simp only [cardinal.mk_denumerable],
end
