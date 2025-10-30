import Game.Metadata
import Game.Levels.Cantor.L06_IsFixedPt_odd

World "Cantor"
Level 7

Title ""

/-
Introduction ""
-/
Introduction "Intro Cantor L07"

/-
Conclusion "
  **Cantor**: Na, seid ihr schon fertig??

  **Robo**:  Einen Zettel haben wir noch.
"
-/
Conclusion "`CONC`Conclusion Cantor L07"

open Function Set

/-
  planned to be used as `range_fixedPoints` for future planet on quotients;
  don't need a name for now
-/
Statement {A : Type} (f : A → A) (h : f ∘ f = f) :
    range f = fixedPoints f := by
  /-
  Hint "
    **Robo**:  Fang am besten damit an, wieder alle Definition auszuschreiben.
    Ich würde sagen:  `unfold range fixedPoints IsFixedPt`.
    Und die Annahme `{h}` könntest du schon einmal `congr_fun` genauer ausschreiben.
    "
  -/
  Hint "Try `unfold range fixedPoints IsFixedPt` and rewrite assumption `{h}` firstly by `congr_fun`"
  unfold range fixedPoints IsFixedPt
  /-
  Hint (hidden := true) (strict := true) "
    **Robo**:  Ich meinte `apply congr_fun at h`.
  "
  -/
  Hint "Try `apply congr_fun at h`"
  apply congr_fun at h
  /-
  Hint (hidden := true) (strict := true) "
    **Robo**:  Vielleicht fängst du mal wieder mit `ext` an.
    Oder mit `Subset.antisymm_iff`.
    "
  -/
  Hint "Try `ext` | `Subset.antisymm_iff`"
  Branch
    rw [Subset.antisymm_iff]
    simp
    constructor
    · assumption
    · intro a ha
      use a
  ext a
  simp
  constructor
  · intro ⟨y, hy⟩
    rw [← hy]
    specialize h y
    clear hy
    /- Hint (hidden := true) "**Robo**:  Hilft vielleicht `comp_apply`?  Oder `simp`?" -/
    Hint "Try `comp_apply` | `simp`"
    simp at h -- or: rw [comp_apply] at h
    assumption
  · intro ha
    use a


TheoremTab "Function"
