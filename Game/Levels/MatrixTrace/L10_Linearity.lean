import Game.Levels.MatrixTrace.L09_Characterize

--import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Trace"
Level 10

Title "Trace"

Introduction
"
Tracy kommt zu euch hin und fängt an mit euch zu spielen. Belustigt gibt es euch verschiedenste
Aufgaben und Terme, und ihr versucht diese schnell genug zu kombinieren.
"

Conclusion "Nach einem längeren spielhaften Austausch über Matrizen, deren Spur, und
Standardbasen, beschliesst ihr auch auf den Rückweg zu machen.

Ihr verlauft euch sofort, doch Tracy ist euch offenbar gefolgt und führt euch queer durch
die Grasslandschaft schnurstrakts zu eurem Schiff zurück."

open Matrix BigOperators Fintype

Statement {n : ℕ} {t : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) :
    trace (A - t • 1) = trace A - t • n := by
  Hint "**Du**: Da geht es gerade offensichtlich um Linearität der Spur von Matrizen."
  rw [trace_sub]
  rw [trace_smul]
  rw [trace_one]
  Hint "**Robo**: Dieser letzte Schritt ist `Fintype.card_fin`. Das ginge auch alles
  mit `simp` wenn wir nicht am spielen wären.

  **Du**: Ist doch egal, das macht Spass!"
  rw [card_fin]

/---/
TheoremDoc Matrix.trace_one as "trace_one" in "Matrix"

/---/
TheoremDoc Matrix.trace_smul as "trace_smul" in "Matrix"

/---/
TheoremDoc Matrix.trace_sub as "trace_sub" in "Matrix"

NewTheorem Matrix.trace_one Matrix.trace_smul Matrix.trace_sub
OnlyTactic rw
TheoremTab "Matrix"