-- Level name : Aufgabe

import data.real.basic
import algebra.module.submodule.lattice
import linear_algebra.basic
--import algebra.algebra.basic

variables {R V : Type*} [field R] [add_comm_group V] [module R V]
variables (p : V →ₗ[R] V)

/- Lemma
Beweise.
-/
example (h : p ∘ p = p) : p.ker ⊔ p.range = ⊤ :=
begin
  rw eq_top_iff,
  intros v hv,

  rw ←sub_add_cancel v (p v),

  apply submodule.add_mem_sup,
  { rw [linear_map.mem_ker],
    rw [map_sub],
    change p v - (p ∘ p) v = 0,  -- oder: rw [function.comp, function.funext_iff] at h,
    rw h,
    simp },
  { simp }
end