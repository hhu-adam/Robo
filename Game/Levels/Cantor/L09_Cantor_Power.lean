import Game.Metadata
import Game.Levels.Cantor.L02_IsFixedPt_not

World "Cantor"
Level 9

Title "Cantor"

Introduction
"
**Cantor**: Wie gesagt, es gibt keine surjektive Funktion `A → Set A`, ist das nicht
wunderbar!

"

open Set Function

Statement cantor_power {A : Type*} : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  Hint (hidden := true) "Widerspruch."
  by_contra h
  Branch
    apply not_isFixedPt_not -- Lvl 2
    Branch
      -- Mathlib states one should not use the fact that `Set A` is `A → Prop`. Instead
      -- one should use `(· ∈ ·)` and `setOf`. This would looks like the following:
      let g : A → A → Prop := fun (a b : A) => (b ∈ f a)
      apply cantor_diagonal g h (fun x => ¬x)
    Branch
      apply cantor_diagonal f h (fun x => ¬x)
    apply cantor_diagonal -- Lvl 7
    assumption
  Hint "Überleg mal, wie man `cantor_diagonal` von vorhin verwenden kann."
  Hint (hidden := true) "Zum Beispiel mit `apply cantor_diagonal at {h}`!"
  apply cantor_diagonal at h
  Hint "Welche Funktion `Prop → Prop` kennst du denn die keinen Fixpunkt hat?"
  Hint (hidden := true) "Wie wäre es mit `fun (A : Prop) ↦ ¬ A`?"
  let s := (¬ ·)
  have hs := h s
  have n_hs := not_isFixedPt_not
  contradiction


TheoremTab "Function"
