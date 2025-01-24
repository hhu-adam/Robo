-- Level name : Basis

import vectorspace.basis.basis

notation `ℝ²` := fin 2 → ℝ

/- Lemma
Zeige, dass `![1, 0], ![1, 1]` den ganzen `ℝ`-Vektorraum `ℝ²` aufspannt.
-/
example : my_basis 0 = ![1, 0] :=
begin
  apply basis.mk_apply,
end
