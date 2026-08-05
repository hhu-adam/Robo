import Game.Levels.Samarkand.L05_InjectiveFibre

open Function Set FullGrind

World "Samarkand"
Level 6

Title ""

-- Introduction "**Arapuka**: Und wie sieht es hiermit aus?"
Introduction "Intro Samarkand L06"

Statement {A B : Type} (f : A → B)  (y : B) :
     f ⁻¹' {y} ≠ ∅ ↔ (∃ a, f a = y) := by
  /-
  Hint "
   **Du**:  Das soll wohl heißen:  die Faser von `b` ist genau dann nicht-leer, wenn `b` ein Urbild besitzt.
   Mal wieder ziemlich offensichtlich.

   **Robo**:  Ja, bis auf Notation.
   Aber zum Glück haben wir schon `eq_empty_iff_forall_notMem` gezeigt.
   Um das anzuwenden, musst du nur das Ungleichheitszeichen auflösen, zum Beispiel einfach mit `unfold Ne`.
  "
  -/
  constructor
  · grind
  · intro h
    obtain ⟨a, ha⟩ := h
    unfold Ne
    rw [eq_empty_iff_forall_notMem]
    simp
    use a

   /-
  Conclusion "
   **Arapuka**: Ihr habt recht.  Da hätte ich selbst drauf kommen können.
  "
  -/

  Conclusion "Conclusion Samarkand L06"
