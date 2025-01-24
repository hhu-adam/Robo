-- Level name : Lineare Unabhängigkeit

import algebra.module.submodule.lattice
import data.real.basic            -- definiert `ℝ`
import data.matrix.notation       -- Importiert Matrix/Vektor-Notation
import linear_algebra.finsupp

import algebra.big_operators.default
import linear_algebra.basis

notation `ℝ²` := fin 2 → ℝ

/- Lemma
Zeige, dass `![1, 0], ![1, 1]` linear unabhängig über `ℝ` sind.
-/
lemma my_basis_lin_indep : linear_independent ℝ ![(![1, 0] : ℝ²), ![1, 1]] :=
begin
  rw fintype.linear_independent_iff,
  intros c h,
  simp at h,
  intros i,
  fin_cases i,
  swap,
  { exact h.2 },
  { have h' := h.1,
    rw [h.2, add_zero] at h',
    exact h'}
end
