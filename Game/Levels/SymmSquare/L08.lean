import Game.Metadata
import Game.Levels.SymmSquare.L07

World "Symmetric Square"
Level 8

Introduction "Intro Symm L08"

open Function Sym Sym2

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*}

Statement Sym_f_swap (f : Sym2 A → B) : ∀ a b, Sym_f f a b = Sym_f f b a := by
  Hint "[Hint sy8swp] The function `Sym_f` you built in the previous level cannot tell its two
    arguments apart: it only ever looks at the class of `(a, b)`, and swapping the entries does
    not change that class."
  intro a b
  unfold Sym_f
  Hint "[Hint sy8cgr] Both sides apply the same function `f`, so it suffices to show that the
    classes of `(a, b)` and of `(b, a)` agree. This reduction is `congr_arg`."
  apply congr_arg f
  Hint (hidden := true) "[Hint sy8snd] Two classes agree as soon as their representatives are
    equivalent: `Quotient.sound`."
  apply Quotient.sound
  Hint (hidden := true) "[Hint sy8swr] All that is left is the swap rule `Sym2.Rel.swap`."
  apply Sym2.Rel.swap

/--
`Sym_f f` is symmetric in its two arguments: it only ever looks at the class `⟦(a, b)⟧`, and
swapping the two entries does not change that class.
-/
TheoremDoc Sym_f_swap as "Sym_f_swap" in "Quotient"

NewTheorem Sym_f_swap
