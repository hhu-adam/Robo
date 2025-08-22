import Game.Metadata

World "Piazza"
Level 9

Title "" -- "Teilmengen"

Introduction
"
**Sub**:  So, so.  Nur eine Definition!
Und wenn ihr nun mit solchen Inklusionen arbeiten sollt?
"

open Set

Statement {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  -- Hint: do this for understanding the def!
  Hint "
    **Du**:  Kann ich hier auch irgendwie mit `ext` argumentieren?

    **Robo**:  Nein, viel einfacher.  Gib dir einfach mit `intro a` ein beliebiges
    Element aus `A` vor, und zeige, dass es in `C` liegt.

    Aber vielleicht schreibst du vorher doch einmal alle Inklusionen mit
    `rw [subset_iff] at *` aus, damit du siehst, was passiert.
  "

  rw [subset_iff] at *
  -- tauto -- would work here
  intro a ha
  apply h₁ at ha
  apply h₂ at ha
  assumption

DisabledTactic tauto

NewDefinition Subset

TheoremTab "Set"

Conclusion ""
