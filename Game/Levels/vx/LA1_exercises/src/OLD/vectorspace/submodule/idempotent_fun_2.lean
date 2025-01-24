-- Level name : Aufgabe

import vectorspace.submodule.idempotent_fun_1

variables {R V : Type*} [field R] [add_comm_group V] [module R V]
variables (p : V →ₗ[R] V)

/- Lemma
Beweise.
-/
example (h : p ∘ p = p) : p.ker ⊓ p.range = ⊥ :=
begin
  rw eq_bot_iff,
  intros v hv,
  rw submodule.mem_bot,
  rw submodule.mem_inf at hv,
  cases hv.2 with w hw,
  rw ←hw,
  rw ←h,
  change p (p w) = _,
  rw  hw,
  rw ←linear_map.mem_ker,
  exact hv.1,
end
