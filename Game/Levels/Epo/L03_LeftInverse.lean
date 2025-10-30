import Game.Metadata


World "Epo"
Level 3

Title ""

/-
Introduction ""
-/
Introduction "Intro Epo L03"

open Function

Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ LeftInverse f g := by
  /-
  Hint "
  **Du**: Ich vermute mal, das soll heißen, `g` ist genau dann ein Rechtsinverses von `f`, wenn `f` ein Linksinverses von `g` ist.

  **Robo**:  Genau.  Aber wenn mich nicht alles täuscht, ist das in Leansch weniger ein Satz als vielmehr die Definition von `Function.RightInverse`.
  Und dummerweise muss man tatsächlich `Function.RightInverse` statt schlicht `RightInverse` schreiben, weil `RightInverse` in Leansch mehrdeutig ist.
  "
  -/
  Hint "Goal says that `g` is righ inverse of `f` iff `f` is left inverse of `g`.
  Try `Function.RightInverse`. It has to be written as `Function.RightInverse` instead of `RightInverse`
  because `RightInverse` is ambigous in Leanic."
  Branch
    unfold Function.RightInverse
    rfl
  tauto

TheoremTab "Function"
NewDefinition Function.RightInverse Function.LeftInverse
