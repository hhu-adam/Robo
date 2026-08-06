import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Induction
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Cases

/-!
# Modified `induction` tactic

Modify `induction` tactic to support the lean3-style `with` keyword, i.e.
`induction n with d hd`.

This is mainly copied and modified from the mathlib-tactic `induction'`.

Note: displaying `0` instead of `Nat.zero` needs no work here; Lean's
`@[induction_eliminator]` for `Nat` already produces `0` / `n + 1` cases, and
`Game.Metadata.DelaboratorNatSucc` displays closed `Nat.succ` chains as numerals.
-/

open Lean Parser Tactic
open Meta Elab Elab.Tactic
open Mathlib.Tactic

open private getElimNameInfo from Lean.Elab.Tactic.Induction

/--
Modified `induction` tactic for this game.

Usage: `induction n with d hd`.

*(The actual `induction` tactic has a more complex `with`-argument that works differently)*
-/
elab (name := Robo.induction) "induction " tgts:(Parser.Tactic.elimTarget,+)
    usingArg:((" using " ident)?)
    withArg:((" with" (ppSpace colGt binderIdent)+)?)
    genArg:((" generalizing" (ppSpace colGt ident)+)?) : tactic => do
  let (targets, toTag) ← elabElimTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := true)
    let targets ← addImplicitTargets elimInfo targets
    checkInductionTargets targets
    let targetFVarIds := targets.map (·.fvarId!)
    g.withContext do
      let genArgs ← if genArg.1.isNone then pure #[] else getFVarIds genArg.1[1].getArgs
      let forbidden ← mkGeneralizationForbiddenSet targets
      let mut s ← getFVarSetToGeneralize targets forbidden
      for v in genArgs do
        if forbidden.contains v then
          throwError "variable cannot be generalized \
            because target depends on it{indentExpr (mkFVar v)}"
        if s.contains v then
          throwError "unnecessary 'generalizing' argument, \
            variable '{mkFVar v}' is generalized automatically"
        s := s.insert v
      let (fvarIds, g) ← g.revert (← sortFVarIds s.toArray)
      g.withContext do
        let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
        let elimArgs := result.elimApp.getAppArgs
        ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! targetFVarIds
        g.assign result.elimApp
        let subgoals ← ElimApp.evalNames elimInfo result.alts withArg
          (generalized := fvarIds) (toClear := targetFVarIds) (toTag := toTag)
        setGoals <| (subgoals ++ result.others).toList ++ gs
