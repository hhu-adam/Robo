import Game.Levels.Mono.L10_Auxiliary

World "Mono"
Level 11

Title "Injections have a left inverse, and vice versa"

Introduction
"
"

open Function Set

/---/
TheoremDoc Function.injective_iff_hasLeftInverse as "injective_iff_hasLeftInverse" in "Function"

Statement Function.injective_iff_hasLeftInverse {A B : Type} [hA : Nonempty A]  (f : A → B) :
  Injective f ↔ HasLeftInverse f := by
  Hint "
    **Du**:  Ich seh schon.  Die Eposophen wollten gern bewiesen haben, dass eine Abbildung genau dann surjektive ist, wenn sie ein Rechtsinverses besitzt.
    Und die hiesigen Monosophen wollen gern bewiesen haben, dass eine Abbildung genau dann injektiv ist, wenn sie in Linksinverses besitzt.

    **Robo**: Ja, außer dass sie diese zusätzliche Voraussetzung `Nonempty A` brauchen.
  "
  constructor
  · intro hf
    Hint (hidden := true) "
      **Du*:  Ich will ein Linksinverses angeben, aber ich sehe gerade nicht, wie.

      **Robo**:  Erinner dich an die Aussage, die wir eben gerade gezeigt hatten: ` ∀ b : B, ∃ a : A, …`
      Wenn du die hier hättest, könntest du vermutlich mit `choose` das gesuchte Linksinverse wählen.
      Nur hat diese Aussage dummerweise keinen Namen.
      Vielleicht formulierest du sie noch einmal mit `have` selbst aus, und beweist sie auch noch einmal.
    "
    have : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b := by
      /- exactly L10_Auxiliary, now without hints -/
      obtain ⟨a₀⟩ := hA
      intro b
      by_cases hb : ∃ a' : A, f a' = b
      · obtain ⟨a,ha⟩ := hb
        use a
        left
        assumption
      use a₀
      right
      assumption
    choose g hg using this
    use g
    intro a
    apply hf
    obtain hpos | hneg := hg (f a)
    · assumption
    · push_neg at hneg
      have : f a ≠ f a := hneg a
      contradiction
  · /- Injective f → HasLeftInverse f
       exactly L09_injOfHasLeftInv, now without hints-/
    Hint (hidden := true) "
      **Robo**:  Das hatten wir doch auch schon gezeigt …  aber ich hatte vergessen, es abzuspeichern.
      Erinnerst du dich an den Beweis?
    "
    intro hL
    intro a a' ha
    obtain ⟨g, hg⟩ := hL
    apply congr_arg g at ha
    unfold LeftInverse at hg
    rw [hg a, hg a'] at ha
    assumption

Conclusion "
Ihr bekommt wieder eine große Runde Applaus und werdet ihr verabschiedet.
Wieder gibt es keine Transportkapseln für den Rückweg.
Aber so weit ist es ja nun auch wieder nicht.
"
