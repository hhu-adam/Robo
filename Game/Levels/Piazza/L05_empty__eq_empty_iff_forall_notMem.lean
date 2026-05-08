import Game.Metadata

World "Piazza"
Level 5

Title ""

/-
Introduction
"
  **Mem:** Findet ihr diese Aussage auch wieder verwirrend?
"
-/
Introduction "Intro Piazza L05"

namespace Set

Statement : { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  /-
  Hint "
    **Du**: Nein, `∅` kenne ich.

    **Robo**: Um ganz sicher zu gehen, dass du das richtig verstehst,
    könntest du auch mit `rw [eq_empty_iff_forall_notMem]` anfangen.
    Oder mit `simp [eq_empty_iff_forall_notMem]`, falls du schnell fertig werden möchtest.
  "
  -/
  Hint "Having `∅` you could either start with `rw [eq_empty_iff_forall_notMem]` or
  `simp [eq_empty_iff_forall_notMem]`"
  /- Want `eq_empty_iff_forall_notMem` to be introduced here,
     because it is needed in SAMARKAND!
  -/
  Branch
     ext
     simp
  rw [eq_empty_iff_forall_notMem]
  simp

TheoremTab "Set"

/---/
TheoremDoc Set.eq_empty_iff_forall_notMem as "eq_empty_iff_forall_notMem" in "Set"
NewTheorem Set.eq_empty_iff_forall_notMem

NewDefinition Set.empty

Conclusion ""
