import Lean

open Lean Elab Tactic Meta Parser.Tactic Parser.Tactic.Grind

/-! # Restricted `grind`, with a per-level opt-out

Importing this module makes `grind` **restricted everywhere** (it always runs
with `(ematch := 0)`). Every surface form is covered — bare `grind`, config
(`grind (…)`, `grind +flag`, `grind -flag`), `grind only`, `grind [lemmas]`,
and `grind => …`.

To get the full, unrestricted `grind` in a particular level, start the level with

```lean
Statement (preamble := grind_mode 1) …
```

`grind_mode n` adds a hidden hypothesis `GrindMode n` to the goal, which `grind`
then looks up in the local context. Unlike a scoped parser (see the unused
`Game.Metadata.Tactic.Grind`), this works in the live version of lean4game,
since the preamble runs in the same proof as the player's input. The hypothesis
is an implementation detail, so it is not displayed to the player. -/

namespace LevelGrind

/-- Marker. A hidden hypothesis of type `GrindMode n` in the local context
selects the behaviour of `grind`. -/
def GrindMode (_n : Nat) : Prop := True

/-- `grind_mode n` adds a hidden (implementation-detail) hypothesis `GrindMode n`
to the main goal. Mode `1` means full `grind`; anything else means restricted. -/
elab "grind_mode " n:num : tactic => liftMetaTactic1 fun g => do
  let type := mkApp (mkConst ``GrindMode) (mkRawNatLit n.getNat)
  let (h, g) ← (← g.assert `grindMode type (mkConst ``True.intro)).intro1P
  g.withContext do
    let decl ← g.getDecl
    let lctx := (← getLCtx).setKind h .implDetail
    let g' ← withLCtx lctx (← getLocalInstances) <|
      mkFreshExprSyntheticOpaqueMVar decl.type decl.userName
    g.assign g'
    return g'.mvarId!

/-- The grind mode of the current goal (`0` if none was set). -/
def getGrindMode : MetaM Nat := do
  for d in (← getLCtx) do
    if let .app (.const ``GrindMode _) (.lit (.natVal n)) := d.type then
      return n
  return 0

/-- Global, high-priority parser capturing *every* surface form of `grind`. -/
syntax (name := gGrind) (priority := high)
  "grind" optConfig (&" only")? (" [" grindParam,* "]")? (" => " grindSeq)? : tactic

/-- In mode `1`, run the core `grind` unchanged. Otherwise append `(ematch := 0)`
to the config (last, so it overrides any caller value). In both cases the node is
retagged with the core `grind` kind, so the builtin elaborator runs — no recursion. -/
@[tactic gGrind] def evalLevelGrind : Tactic := fun stx => do
  let stx := stx.setKind ``Lean.Parser.Tactic.grind
  if (← withMainContext getGrindMode) == 1 then
    evalTactic stx
  else
    let ematch0 ← `(configItem| (ematch := 0))
    let items := stx[1][0]
    evalTactic (stx.setArg 1 (stx[1].setArg 0 (items.setArgs (items.getArgs.push ematch0.raw))))

end LevelGrind
