import Game.Levels.Samarkand.L08_LeftInvPreimage

World "Samarkand"
Level 9

Title "" -- "Preimage of surjective is injective"

/-
Introduction "
  **Arapuka**:  Könnt ihr mir vielleicht sogar mit dieser Vermutung weiterhelfen?
"
-/
Introduction "Intro Samarkand L09"

open Function FullGrind

/---/
TheoremDoc Set.preimage_injective as "preimage_injective" in "Function"

namespace Set

Statement preimage_injective {A B : Type} {f : A → B} : Injective (preimage f) ↔ Surjective f := by
  /-
  Hint "
    **Robo**:  Eine Abbildung ist genau dann surjektiv, wenn die induzierte Abbildung `preimage f`, die eine Teilmenge auf das Urbild unter dieser Teilmenge wirft, injektiv ist?
    Stimmt das überhaupt?

    **Du**: Ich glaube, ja.  Das habe ich schonmal gesehen.

    **Robo**:  Na dann, los!
  "
  -/
  constructor
  · intro hinj b
    Branch
      -- old proof
      have h : f ⁻¹' {b} ≠ ∅ ↔ (∃ a, f a = b) := by -- see L06_PreimageNonempty
        unfold Ne
        rw [eq_empty_iff_forall_notMem]
        simp
      rw [← h]
      change preimage f {b} ≠ ∅
      have g : f ⁻¹' ∅ = ∅ := by
        simp
      rw [← g]
      rw [Injective.ne_iff hinj]
      simp
    suffices : f ⁻¹' {b} ≠ ∅
    · grind
    have h : f ⁻¹' ∅ = ∅
    · grind
    rw [← h]
    rw [Injective.ne_iff]
    simp
    assumption
  · intro h_surj
    intro s s' hs
    apply congr_arg (image f) at hs
    rw [image_preimage_eq] at hs
    rw [image_preimage_eq] at hs
    · assumption
    · assumption
    · assumption

/-
Conclusion "
  **Arapuka**:  Fantastisch!  Ich bin so aufgeregt, ich möchte am liebsten in die Luft springen.
  Aber das geht natürlich nicht.  Dann ist das Muster futsch.

  **Robo**:  Wie lange hast du denn noch?

  **Arapuka**:  Hier noch drei Jahre, 22 Tage, 7 Stunden und 35 Minuten.

  **Robo**:  Ohh …

  **Du**:  Und woher weißt du, wo genau du danach hingehen musst, damit das Muster passt?

  **Arapuka**:  Ah!

  Über Arapukas Gesicht breitet sich ein großes Lächeln aus.

  **Arapuka**:  Das ist eben die Kunst!
"
-/

Conclusion "Conlsuion Samarkand L09"
