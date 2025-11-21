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
Introduction "`INTRO` Intro Piazza L05"

namespace Set

Statement : { n : ℕ | Even n } ∩ { n : ℕ | Odd n } = ∅ := by
  /-
  Hint "
    **Du**: Nein, `∅` kenne ich.

    **Robo**: Um ganz sicher zu gehen, dass du das richtig verstehst,
    könntest du auch mit `rw [eq_empty_iff_forall_not_mem]` anfangen.
    Oder mit `simp [eq_empty_iff_forall_not_mem]`, falls du schnell fertig werden möchtest.
  "
  -/
  Hint "Having `∅` you could either start with `rw [eq_empty_iff_forall_not_mem]` or
  `simp [eq_empty_iff_forall_not_mem]`"
  /- Want `eq_empty_iff_forall_not_mem` to be introduced here,
     because it is needed in SAMARKAND!
  -/
  Branch
     ext
     simp
  rw [eq_empty_iff_forall_not_mem]
  simp

TheoremTab "Set"

/---/
TheoremDoc Set.eq_empty_iff_forall_not_mem as "eq_empty_iff_forall_not_mem" in "Set"
NewTheorem Set.eq_empty_iff_forall_not_mem

NewDefinition Set.empty

Conclusion ""
