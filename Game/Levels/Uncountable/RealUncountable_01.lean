import Game.Metadata
import Mathlib.SetTheory.Cardinal.Arithmetic

World "TmpRealsUncountable"
Level 1

Title "überabzählbare reele Zahlen"

Introduction "Zuerst zeigen wir ein Hilfslemma."

universe u

open Module

-- Damit man `#K` anstatt `Cardinal.mk K` für die Kardinalität von `K` schreiben kann
namespace Cardinal

/- Sei $K$ ein Körper mit Kardinalität $\aleph_0$ und sei $V$ ein $K$-Vektorraum.

Zeige, dass die Kardinalität von $V \le \aleph_0$. -/

/---/
TheoremDoc Cardinal.cardinal_eq_of_finite_basis as "Cardinal.cardinal_eq_of_finite_basis" in "Cardinal"

Statement cardinal_eq_of_finite_basis {K V ι : Type u} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (h_card : #K = ℵ₀) (h_basis : Basis ι K V) : #V ≤ ℵ₀:= by
  Hint "Als Beweisstrategie möchtest du wie `#K ^ #ι ≤ ℵ₀` gehen. Also zuerst sagen,
  dass die Kardinalität von $V$ genau die Kardinalität von $K$ hoch $\\mathrm\{dim}(V)$ ist."
  Hint "Schau mal `have h := {h_basis}.equivFun.toEquiv` an"
  rw [Cardinal.mk_congr h_basis.equivFun.toEquiv]
  rw [← Cardinal.power_def]
  rw [h_card]
  rw [Cardinal.mk_fintype]
  rw [power_natCast]
  apply Cardinal.power_nat_le
  rfl

  -- simp only [Cardinal.mk_fintype, Cardinal.pow_cast_right]
  -- apply Cardinal.power_nat_le
  -- rfl
  -- TODO: Project by Eduart Bopp

/---/
TheoremDoc Cardinal.mk_congr as "Cardinal.mk_congr" in "Cardinal"

/---/
TheoremDoc Cardinal.power_def as "Cardinal.power_def" in "Cardinal"

/---/
TheoremDoc Cardinal.mk_fintype as "Cardinal.mk_fintype" in "Cardinal"

/---/
TheoremDoc Cardinal.power_nat_le as "Cardinal.power_nat_le" in "Cardinal"

/---/
TheoremDoc Cardinal.power_natCast as "Cardinal.power_natCast" in "Cardinal"

NewTheorem Cardinal.mk_congr Cardinal.power_def Cardinal.mk_fintype
  Cardinal.power_nat_le Cardinal.power_natCast
