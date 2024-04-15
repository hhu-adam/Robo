import Init.ByCases
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Intro

open Lean Meta Elab Tactic

syntax (name := Robo.by_cases) "by_cases " (atomic(ident " : "))? term : tactic

@[tactic Robo.by_cases] def evalByCases : Tactic := fun stx => withMainContext do
  let h ← mkFreshBinderNameForTactic <| (stx[1].getArgs.getD 0 (mkIdent `h) |>.getId)
  let h' : TSyntax `term := ⟨mkIdent h⟩
  let e : TSyntax `term := ⟨stx[2]⟩
  evalTactic (← `(tactic| open Classical in refine (dite $e (fun ($h' : $e) => ?pos) (fun ($h' : ¬ $e) => ?neg))))-- if $h' : $e then ?pos else ?neg))
