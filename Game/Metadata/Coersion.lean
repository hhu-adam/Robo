import Lean
import Mathlib.Algebra.BigOperators.Basic

/-!

# Macro / Elaborator

This file defines a custom macro dealing with
coersion `Fin n → Nat` inside a sum.

In paricularly a sum `∑ (i : Fin n), i + 1` is elaborated as `∑ (i : Fin n), (i : ℕ) + 1`
so no summation ever happens in `Fin n` but always at least in `ℕ`.

# Delaborator

Further, there is a delaborator for coersions which removes the `↑`.

*Note*: This might cause problems, because the delaborated term might not parse anymore,
but the aim is to test how relevant this is in the scope of this game.
-/


open Lean BigOperators

namespace BigOperators

/-- Traverse Syntax recursively replacing all `i` with `(i : ℕ)`. -/
unsafe def addNatCoe' (p : Term) (i : Ident) : Term := { raw :=
  match p.raw with
  | .missing => .missing
  -- If we have a function application, Lean should be able to figure out the
  -- type without any hints.
  -- This also allows for sums of matrices to parse.
  | .node _ `Lean.Parser.Term.app _ => p.raw
  -- Equality should be a function application too, but `a = b` and `Eq a b`
  -- seem to be apriory different terms, so we exclude the former
  | .node _ `«term_=_» _ => p.raw
  -- On encountering a coersion of the form `(_ : Fin _)` we should stop
  | .node _ `Lean.Parser.Term.typeAscription #[_, _, _, .node _ `null #[.node _ `Lean.Parser.Term.app #[.ident _ _ `Fin _, _]], _] =>
    p.raw
  | .node info kind args =>
    -- go recursively into each node
    .node info kind (args.map (addNatCoe' ⟨·⟩ i))
  | .atom _ _ => p.raw
  | .ident info _ _ _ =>
    -- if the ident is `i`, then replace it with `(i : ℕ)`.
    if p == i then
      .node info `Lean.Parser.Term.typeAscription
        #[.atom info "(", p.raw, .atom info ":", .node info `null
          #[.node info `termℕ #[.atom info "ℕ"]], .atom info ")"]
    else
      p.raw
}

@[implemented_by addNatCoe', inherit_doc addNatCoe']
def addNatCoe (p : Term) (i : Ident) : Term := p

-- Note: must be scoped in `BigOperators` because otherwise, apparently the original
-- macro takes priority.
/-- Custom macro to interpret all sums in `ℕ` instead of possible `Fin n`. -/
scoped macro_rules (kind := BigOperators.bigsum)
  | `(∑ $i:ident, $body) => `(Finset.sum Finset.univ (fun $i:ident ↦ $(addNatCoe body i)))
  | `(∑ $i:ident : $t, $body) => `(Finset.sum Finset.univ (fun $i:ident : $t ↦ $(addNatCoe body i)))

open Lean PrettyPrinter.Delaborator SubExpr in

/-- Custom coersion delaborator that does not display a `↑`. -/
@[delab app]
def coeDelaborator : Delab := whenPPOption getPPCoercions do
  let e ← getExpr
  let .const declName _ := e.getAppFn | failure
  let some info ← Meta.getCoeFnInfo? declName | failure
  let n := e.getAppNumArgs
  withOverApp info.numArgs do
    match info.type with
    | .coe => `($(← withNaryArg info.coercee delab)) -- ↑
    | .coeFun =>
      if n = info.numArgs then
        `(⇑$(← withNaryArg info.coercee delab))
      else
        withNaryArg info.coercee delab
    | .coeSort => `(↥$(← withNaryArg info.coercee delab))
