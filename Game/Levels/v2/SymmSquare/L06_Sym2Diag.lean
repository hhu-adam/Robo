import Game.Metadata


World "Symmetric Square"
Level 6

Title "Unordered pairs on diagonal"

Introduction
"
We shall henceforth use the notation `s(x, y)` for the quotient element `⟦(x, y)⟧` of `Sym2 A`.

By definition `s(x, y)` is the unordered pair of `x` and `y`. That is, `s(x, y) = s(y, x)`.

An an element of `Sym2 α` is on the diagonal if it is of the form `(a, a)`.
"

open Sym2

-- example {α : Type*} (s : Sym2 α) (sdiag : Sym2.IsDiag s) : { s : Finset α | s.card = 1} := by
--   sorry
