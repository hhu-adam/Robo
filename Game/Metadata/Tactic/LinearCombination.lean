import Mathlib.Tactic.LinearCombination
import Game.Metadata.Tactic.Ring

/-!
Only modification from Mathlib is that we use (our modified) `ring` instead of `ring1` as the
default norm.
-/

open Mathlib.Tactic.LinearCombination
open Lean Elab Term

/-- Implementation of `linear_combination` and `linear_combination2`. -/
def Game.elabLinearCombination
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e => withSynthesize do
    match ← expandLinearCombo e with
    | none => `(Eq.refl $e)
    | some p => pure p
  let norm := norm?.getD (Unhygienic.run `(tactic| ring))
  Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
    match exp? with
    | some n =>
      if n.getNat = 1 then `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
      else `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
    | _ => `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))

elab_rules : tactic
  | `(tactic| linear_combination $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    Game.elabLinearCombination tac n e
