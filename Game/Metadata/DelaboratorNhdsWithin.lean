import Mathlib.Topology.Defs.Filter

open Lean Meta PrettyPrinter Delaborator SubExpr Topology

/-!
Display one-sided neighbourhood filters with Mathlib's `𝓝[≤]` notation,
e.g. `𝓝 0 ⊓ 𝓟 {x | x ≤ 0}` is shown as `𝓝[≤] 0`.
-/

/-- The one-sided neighbourhoods that have a Mathlib notation `𝓝[…] a`. -/
private inductive NhdsSide
  | le | lt | ge | gt | ne

/-- Render `𝓝 a ⊓ 𝓟 {x | x ≤ a}` as `𝓝[≤] a`, and similarly for `<`, `≥`, `>`, `≠`. -/
@[app_delab Min.min]
def delabNhdsInfPrincipal : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs == 4
  let n := e.appFn!.appArg!
  let s := e.appArg!
  guard <| n.isAppOfArity ``nhds 3 && s.isAppOfArity ``Filter.principal 2
  let S := s.appArg!
  guard <| S.isAppOfArity ``setOf 2
  let .lam _ _ body _ := S.appArg! | failure
  let some side ← side? n.appArg! body | failure
  let a ← withAppFn <| withAppArg <| withAppArg delab
  match side with
  | .le => `(𝓝[≤] $a)
  | .lt => `(𝓝[<] $a)
  | .ge => `(𝓝[≥] $a)
  | .gt => `(𝓝[>] $a)
  | .ne => `(𝓝[≠] $a)
where
  /-- Match `body` (of `fun x ↦ body`) against `x ≤ a`, `a < x`, `x ≠ a`, etc. -/
  side? (a body : Expr) : MetaM (Option NhdsSide) := do
    -- `t` is the point `a` (and does not mention the bound variable `x`)
    let isA (t : Expr) : MetaM Bool := do
      if t.hasLooseBVars then return false
      if t == a then return true
      -- new mctx depth: printing must not assign metavariables of the goal
      withNewMCtxDepth <| withReducible <| isDefEq t a
    -- `l R r` is `x R a` (giving `left`) or `a R x` (giving `right`)
    let orient (l r : Expr) (left right : NhdsSide) : MetaM (Option NhdsSide) := do
      if l == .bvar 0 && (← isA r) then return some left
      if r == .bvar 0 && (← isA l) then return some right
      return none
    match body.getAppFn.constName?, body.getAppArgs with
    | some ``LE.le, #[_, _, l, r] => orient l r .le .ge
    | some ``LT.lt, #[_, _, l, r] => orient l r .lt .gt
    | some ``GE.ge, #[_, _, l, r] => orient l r .ge .le
    | some ``GT.gt, #[_, _, l, r] => orient l r .gt .lt
    | some ``Ne, #[_, l, r] => orient l r .ne .ne
    | _, _ => return none
