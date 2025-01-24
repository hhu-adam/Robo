import Game.Metadata
import Game.Levels.SetTheory.L03_Subset


World "SetTheory"
Level 4

Title "Teilmengen"

Introduction
"
Etwas weiter kommt ihr an einem kleinen Gemüsestand vorbei. Da ihr nicht so
richtig einen Plan habt, fragt ihr den Verkäufer.

**Verkäufer**: Hier ist was ganz Wichtiges, was ihr noch oft brauchen werdet:
Ein zentrales Lemma ist `Subset.antisymm_iff` welches folgendes sagt:

```
lemma antisymm_iff {α : Type} {A B : Set α} :
  A = B ↔ A ⊆ B ∧ B ⊆ A
```

**Verkäufer**: Fast immer wenn man Gleichheiten von Mengen zeigen muss, will
man diese in zwei Ungleichungen aufteilen. Hier, ich gebe euch mal ein
Beispiel:
"

open Set Subset

Statement Set.subset_empty_iff {A : Type _} (s : Set A) :
    s ⊆ ∅ ↔ s = ∅ := by
  Hint "**Du**: Ja, die einzige Teilmenge der leeren Menge ist die leere Menge.
  Das wird schon stimmen.

  **Verkäufer**: Also zeig mir das mal!"
  Hint (hidden := true) "**Robo**: Fang doch einmal mit `constructor` an."
  constructor
  · intro h
    Hint "**Verkäufer**: Jetzt könnt ihr mein Lieblingslemma brauchen!

    Dann sind `s ⊆ ∅` und `∅ ⊆ s` separat zu zeigen."
    Branch
      -- alternative
      apply Subset.antisymm
    rw [Subset.antisymm_iff]
    Branch
      constructor
      · assumption
      · simp only [empty_subset]
    tauto
  · intro h
    Hint (hidden := true) "**Robo**: Was kann man denn mit `{h}` jetzt machen?

    **Du**: Wenn ich damit umschreibe erhalte ich `∅ ⊆ ∅`.

    **Robo**: Was `rw` als Reflexivität direkt löst!
    "
    -- TODO: Is it confusing that `rw` closes this?
    rw [h]

Conclusion ""

/---/
TheoremDoc Set.Subset.antisymm_iff as "Subset.antisymm_iff" in "Set"

DisabledTactic tauto
NewTheorem Set.Subset.antisymm_iff Set.empty_subset
TheoremTab "Set"
