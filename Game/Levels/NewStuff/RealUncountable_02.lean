import Game.Metadata
import Game.Levels.NewStuff.RealUncountable_01

set_option autoImplicit false

World "TmpRealsUncountable"
Level 2

Title "überabzählbare reele Zahlen"

Introduction
"
Wir zeigen dass ℝ ein nicht-endlicher ℚ-Vektorraum ist.
"


universe u

-- Damit man `#K` anstatt `Cardinal.mk K` für die Kardinalität von `K` schreiben kann
namespace Cardinal

/--
Zeige dass ℝ kein endlich dimensionaler ℚ-Vektorraum ist.
-/
Statement : ¬ FiniteDimensional ℚ ℝ := by
  intro h
  -- Widerspruch: Wir wissen dass ℝ nicht countable ist.
  apply Cardinal.not_countable_real
  rw [← Cardinal.le_aleph0_iff_set_countable]
  rw [Cardinal.mk_univ]
  set B := Basis.ofVectorSpace ℚ ℝ
  convert cardinal_eq_of_finite_basis _ B
  simp only [Cardinal.mk_denumerable]

NewTheorem Cardinal.not_countable_real Cardinal.le_aleph0_iff_set_countable
  Cardinal.mk_univ Cardinal.cardinal_eq_of_finite_basis Cardinal.mk_denumerable

NewDefinition Basis.ofVectorSpace
