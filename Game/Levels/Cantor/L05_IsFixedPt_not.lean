import Game.Metadata
import Game.Levels.Cantor.L04_fixedPoints_neg

World "Cantor"
Level 5

Title ""

Introduction ""

/-
Conclusion "
  **Cantor**: Ihr kommt der Sache näher …

   Die Spatzen sind – wenig überraschend – davon geflogen.
   Also jongliert er wieder mit den Kakteen, und fährt dabei Einrad.
"
-/
Conclusion "Conclusion Cantor L05"

open Function Set

Statement : ¬ ∃ (P : Prop),  IsFixedPt (¬ .) P := by
  /-
  Hint "**Du**: Was bedeutet das zweite `¬` hier?

  **Robo**:  Dasselbe wie das erste: logische Negation.
  Die kannst du als Selbstabbildung der Menge `Prop` aller möglichen Aussagen auffassen.
  Und diese Abbildung hat natürlich keine Fixpunkte,
  denn eine Aussage kann doch nicht gleich ihrer Negation sein!
  "
  -/
  Hint "The second `¬` means the same as the first: logical negation. Interpret it as the self
  mapping of the set `Prop` of all possible satements."
  Branch
    by_contra h
    obtain ⟨P, hP⟩ := h
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
  simp -- or: tauto, but `simp` is better as we want to repeat this proof with `simp at` later
