-- Level name : Erbsenzählen

import linear_algebra.dimension
import linear_algebra.finite_dimensional
import field_theory.cardinality

variables {𝔽ₚ V : Type*} [field 𝔽ₚ] [fintype 𝔽ₚ] [add_comm_group V] [module 𝔽ₚ V] [fintype V]

-- Tell Lean to use that `V` has finitely many elements, so we can use `‖V‖` below.
-- noncomputable instance V_fintype : fintype V := finite_dimensional.fintype_of_fintype 𝔽ₚ V

local notation `‖` x `‖` := fintype.card x
local notation `dim` := finite_dimensional.finrank  -- or: module.rank 𝔽ₚ V? (they are equal:`finite_dimensional.finrank_eq_dim`)

/- Lemma
Beweise.
-/
example : ‖V‖ = ‖𝔽ₚ‖ ^ (dim 𝔽ₚ V) :=
begin
  set b : basis _ 𝔽ₚ V := basis.of_vector_space 𝔽ₚ V,

  convert module.card_fintype b,
  exact finite_dimensional.finrank_eq_card_basis b,
end
