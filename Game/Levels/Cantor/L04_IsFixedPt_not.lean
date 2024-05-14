import Game.Metadata
import Game.Levels.Cantor.L03_fixedPoints_neg

World "Cantor"
Level 5

Title "Keine Fixpunkte"

Introduction
"**Cantor**: Aber auf was ich eigentlich hinaus wollte, ist die Fixpunkte von `¬` anzuschauen;
Es gibt nämlich keine!"

Conclusion "**Du**: Und was hatten jetzt Fixpunkte mit dem Diagonalargument zu tun?

**Cantor**: Nur Geduld! Ich habe gerade so viel Spaß!"

open Function Set

Statement not_isFixedPt_not : ¬ ∃ (P : Prop),  IsFixedPt (¬ .) P := by
  Hint "**Du**: Ja, `¬(·)` hat keinen Fixpunkt, keine Aussage kann gleichzeitig
    wahr und falsch sein!"
  Branch
    by_contra h
    rcases h with ⟨P, hP⟩
    unfold IsFixedPt at hP
    simp at hP -- a bit magical
  Branch
    push_neg
    intro P h
    unfold IsFixedPt at h
    Branch
      simp_all only [eq_iff_iff]
      simp only [not_iff_self] at h
    tauto
  unfold IsFixedPt
  tauto

TheoremTab "Function"
