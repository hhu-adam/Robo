import Game.Metadata

World "TmpRealsUncountable"
Level 1

Title "überabzählbare reele Zahlen"

Introduction "Zuerst zeigen wir ein Hilfslemma."

universe u

-- Damit man `#K` anstatt `Cardinal.mk K` für die Kardinalität von `K` schreiben kann
namespace Cardinal

/-- Sei $K$ ein Körper mit Kardinalität $\aleph_0$ und sei $V$ ein $K$-Vektorraum.

Zeige, dass die Kardinalität von $V \le \aleph_0$. -/
Statement cardinal_eq_of_finite_basis {K V : Type u} {ι : Type u} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (h_card : #K = ℵ₀) (h_basis: Basis ι K V) : #V ≤ ℵ₀:= by
  Hint "Als Beweisstrategie möchtest du wie `#K ^ #ι ≤ ℵ₀` gehen. Also zuerst sagen,
  dass die Kardinalität von $V$ genau die Kardinalität von $K$ hoch $\\mathrm\{dim}(V)$ ist."
  Hint "Schau mal `have h := {h_basis}.equivFun.toEquiv` an"
  rw [Cardinal.mk_congr (h_basis.equivFun.toEquiv)]
  rw [← Cardinal.power_def]
  rw [h_card]
  simp only [Cardinal.mk_fintype, Cardinal.pow_cast_right]
  apply Cardinal.power_nat_le
  rfl
  -- TODO: Project by Eduart Bopp

NewTheorem Cardinal.mk_congr Cardinal.power_def Cardinal.mk_fintype
  Cardinal.pow_cast_right Cardinal.power_nat_le
