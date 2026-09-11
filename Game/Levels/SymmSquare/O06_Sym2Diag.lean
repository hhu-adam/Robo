import Game.Metadata


World "Symmetric Square"
Level 6

Introduction "Intro Symm O06"

open Sym2

Statement {α : Type*} (s : Sym2 α) (sdiag : Sym2.IsDiag s) : { s : Finset α | s.card = 1} := by
  Hint "[Hint o06diag] From now on we write `s(x, y)` for the class `⟦(x, y)⟧`, the unordered
    pair of `x` and `y`; by construction `s(x, y) = s(y, x)`. Such a pair lies on the
    *diagonal* when it is of the form `s(a, a)`, and then it really carries just the single
    element `a`."
  use {s.diagElem sdiag}
  exact Finset.card_singleton _
