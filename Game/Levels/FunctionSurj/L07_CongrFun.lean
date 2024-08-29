import Game.Metadata


World "FunctionSurj"
Level 7

Title ""


Introduction
"
"

open Function

Statement (f g : ℤ → ℤ) (h : f = g) (x : ℤ) : f x = g x := by
  -- funext at h
  Hint "`apply congr_fun at {h}` ändert `{h} : {f} = {g}` zu
  `{h} : ∀ x, {f} x = {g} x`."
  apply congr_fun at h
  Branch
    have hx := h x --
    assumption
  apply h

/---/
TheoremDoc congr_fun as "congr_fun" in "Function"


OnlyTactic apply assumption «have»
NewTheorem congr_fun
TheoremTab "Function"

Conclusion ""
