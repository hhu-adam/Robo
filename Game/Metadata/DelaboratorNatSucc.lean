import Lean

open Lean PrettyPrinter Delaborator SubExpr

/-!
Display closed `Nat.succ` chains as numerals in the infoview,
e.g. `(Nat.succ 0).succ` is shown as `2`.

This is display-only: the underlying term is unchanged, so tactics like
`rw` still see the `Nat.succ` form. Open terms like `n.succ` are not
affected and keep their default printing.
-/

/-- Render a closed chain of `Nat.succ` applications as a numeral. -/
@[app_delab Nat.succ]
def delabNatSuccNumeral : Delab := do
  let some n := toNat? (← getExpr) | failure
  return quote n
where
  /-- Evaluate a closed `Nat.succ` chain to a `Nat`, if possible.
  The base of the chain may be `Nat.zero`, a raw literal, or an
  `OfNat.ofNat` literal (handled by `Expr.nat?`). -/
  toNat? : Expr → Option Nat
    | .app (.const ``Nat.succ _) a => (toNat? a).map (· + 1)
    | .const ``Nat.zero _ => some 0
    | e => e.nat?
