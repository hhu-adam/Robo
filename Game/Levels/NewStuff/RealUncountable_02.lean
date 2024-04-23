import Game.Metadata
import Game.Levels.NewStuff.RealUncountable_01

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
  Branch
    -- TODO: Eduart Bopp's Beweis
    Hint "
    `let B := Basis.ofVectorSpace ℚ ℝ` gibt dir eine Basis von $\\mathbb\{R}$ über $\\mathbb\{Q}$.
    Mache dann einen Widerspruchsbeweis und brauche folgende Resultate:

    * `Cardinal.not_countable_real`: Das Hilfslemma von vorhin.
    * `Cardinal.not_countable_real` : $\\mathbb\{R}$ ist überabzählbar.

    Fange vielleicht auch damit an, `#ℚ = ℵ₀` zu zeigen.
    "
    let B := Basis.ofVectorSpace ℚ ℝ
    -- beginnt Gegenbeweis
    by_contra
    -- Angenomme R wäre ein endlich dimensionaler ℚ-Vektorraum ist.

    -- Mein Teil

    -- Schreibe die Kardinalität von `ℚ` als ℵ₀
    have h_ℚ : #ℚ = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 ℚ

    -- Anwenden des Lemmas auf die Basis `B` von `ℝ` über `ℚ`
    --#R <= #Q
    have cardinal_ineq : #ℝ ≤ Cardinal.aleph0 :=
      cardinal_eq_of_finite_basis h_ℚ B

    -- R überabzählbar
    have h3 := Cardinal.not_countable_real

    -- ¬#↥set.univ ≤ ℵ₀, set.univ = R
    rw [← Cardinal.le_aleph0_iff_set_countable] at h3
    -- schreibe um zu ¬#ℝ ≤ ℵ₀
    simp only [Cardinal.mk_univ] at h3

    -- Q abzählbar, widerspruch
    contradiction

  by_contra h
  -- Widerspruch: Wir wissen dass ℝ nicht countable ist.
  apply Cardinal.not_countable_real
  rw [← Cardinal.le_aleph0_iff_set_countable]
  rw [Cardinal.mk_univ]
  let B := Basis.ofVectorSpace ℚ ℝ
  apply cardinal_eq_of_finite_basis _ B
  simp only [Cardinal.mk_denumerable]

NewTheorem Cardinal.not_countable_real Cardinal.le_aleph0_iff_set_countable
  Cardinal.mk_univ Cardinal.cardinal_eq_of_finite_basis Cardinal.mk_denumerable
  Cardinal.mk_le_aleph0_iff Cardinal.mk_le_aleph0_iff

NewDefinition Basis.ofVectorSpace
