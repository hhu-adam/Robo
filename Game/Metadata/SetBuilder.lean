/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
import Game.Metadata.FromMathlib
import Game.Metadata.ExtendedBinder

open Lean PrettyPrinter.Delaborator SubExpr in

@[delab app.Finset.filter] def delabFinsetFilter : Delab :=
  whenPPOption getPPNotation do
  let #[_, p, _, t] := (← getExpr).getAppArgs | failure
  guard p.isLambda
  let i ← withNaryArg 1 <| withBindingBodyUnusedName (pure ⟨·⟩)
  let p ← withNaryArg 1 <| withBindingBody i.getId delab
  if t.isAppOfArity ``Finset.univ 2 then
    if ← getPPOption getPPFunBinderTypes then
      let ty ← withNaryArg 0 delab
      `({$i:ident : $ty | $p})
    else
      `({$i:ident | $p})
  -- check if `t` is of the form `s₀ᶜ`, in which case we display `x ∉ s₀` instead
  else if t.isAppOfArity ``HasCompl.compl 3 then
    let #[_, _, s₀] := t.getAppArgs | failure
    -- if `s₀` is a singleton, we can even use the notation `x ≠ a`
    if s₀.isAppOfArity ``Singleton.singleton 4 then
      let t ← withNaryArg 3 <| withNaryArg 2 <| withNaryArg 3 delab
      `({$i:ident ≠ $t | $p})
    else
      let t ← withNaryArg 3 <| withNaryArg 2 delab
      `({$i:ident ∉ $t | $p})
  else
    let t ← withNaryArg 3 delab
    `({$i:ident ∈ $t | $p})

macro_rules
  | `({ $x:ident ∈ $b | $p }) => `(Finset.filter (fun $x => $p) $b)
-/
