import Game.Levels.Samarkand.L07_LeftInvPreimage

World "Samarkand"
Level 8

Title "" -- "Preimage of surjective is injective"

Introduction "
  **Arapuka**:  Könnt ihr mir vielleicht sogar mit dieser Vermutung weiterhelfen?
"

open Function

/---/
TheoremDoc Set.preimage_injective as "preimage_injective" in "Function"

namespace Set

Statement preimage_injective {A B : Type} {f : A → B} : Injective (preimage f) ↔ Surjective f := by
  Hint "
    **Robo**:  Eine Abbildung ist genau dann surjektiv, wenn die induzierte Abbildung `preimage f`, die eine Teilmenge auf das Urbild unter dieser Teilmenge wirft, injektiv ist?
    Stimmt das überhaupt?

    **Du**: Ich glaube, ja.  Das habe ich schonmal gesehen.

    **Robo**:  Na dann, los!
  "
  constructor
  · Branch
      intro h_inj
      intro b
      by_contra h_contra
      push_neg at h_contra
      have h : preimage f {b} = ∅ := by
        rw [eq_empty_iff_forall_not_mem]
        intro a
        specialize h_contra a
        assumption
      have : preimage f ∅ = preimage f {b}
      rw [preimage_empty,h]
      apply h_inj at this
      symm at this
      rw [eq_empty_iff_forall_not_mem] at this
      apply this b
      simp
    intro hinj y
    have h : f ⁻¹' {y} ≠ ∅ ↔ (∃ a, f a = y) := by -- see L06_PreimageNonempty
      unfold Ne
      rw [eq_empty_iff_forall_not_mem]
      simp
    rw [← h]
    -- change f ⁻¹' {y} ≠ ∅ -- TODO: it's displayed not nicely :(
    have g : f ⁻¹' ∅ = ∅ := by
      simp
    rw [← g]
    -- or: `rw [← preimage_empty]`
    rw [Injective.ne_iff hinj]
    simp
  · intro h_surj
    intro s s' hs
    apply congr_arg (image f) at hs
    rw [Surjective.image_preimage h_surj] at hs
    rw [Surjective.image_preimage h_surj] at hs
    assumption

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
