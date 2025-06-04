import Lean

open Lean PrettyPrinter.Delaborator

--     We don't want to dislplay “match x with …”

/-- Delaborator for functions on products like `α × β → γ`. -/
@[delab lam]
def delabLamTuple : Lean.PrettyPrinter.Delaborator.Delab :=
  -- TODO: add the right options from Lean.PrettyPrinter.Delaborator.Options
  -- here, so that `set_option pp.XXX` has de desired effect.
  whenPPOption getPPNotation do
  let stx ← delabLam
  match stx with
  | `(fun $x:ident ↦ match $x₁:ident with | ($m, $n) => $body) =>
    guard <| x.getId == x₁.getId
    `(fun ($m, $n) ↦ $body)
  | _ => pure stx
