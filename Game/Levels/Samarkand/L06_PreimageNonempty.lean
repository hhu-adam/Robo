import Game.Levels.Samarkand.L05_InjectiveFibre

open Function Set

World "Samarkand"
Level 6

Title ""

-- Introduction "**Arapuka**: Und wie sieht es hiermit aus?"
Introduction "`INTRO` Intro Samarkand L06"

Statement {A B : Type} (f : A → B)  (y : B) :
     f ⁻¹' {y} ≠ ∅ ↔ (∃ a, f a = y) := by
  /-
  Hint "
   **Du**:  Das soll wohl heißen:  die Faser von `b` ist genau dann nicht-leer, wenn `b` ein Urbild besitzt.
   Mal wieder ziemlich offensichtlich.

   **Robo**:  Ja, bis auf Notation.
   Aber zum Glück haben wir schon `eq_empty_iff_forall_not_mem` gezeigt.
   Um das anzuwenden, musst du nur das Ungleichheitszeichen auflösen, zum Beispiel einfach mit `unfold Ne`.
  "
  -/
  Hint "Explain `b`. Explain `eq_empty_iff_forall_not_mem`. Try `unfold Ne`"
  unfold Ne
  rw [eq_empty_iff_forall_not_mem]
  simp

   /-
  Conclusion "
   **Arapuka**: Ihr habt recht.  Da hätte ich selbst drauf kommen können.
  "
  -/

  Conclusion "`CONC` Conclusion Samarkand L06"
