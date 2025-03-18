import Game.Metadata.FromMathlib

-- mathlib PR: ………
theorem Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

-- mathlib PR: #19255
alias _root_.Nat.prime_def := Nat.prime_def_lt''



/-! # Delab Problems -/
/-
open BigOperators
open Lean PrettyPrinter Delaborator SubExpr

@[delab app.Finset.sum]
def delabFinsetSum : Delab := do
  guard $ (← getExpr).getAppNumArgs == 5
  guard $ ((← getExpr).getArg! 3).isAppOf' ``Finset.univ
  guard $ ((← getExpr).getArg! 4).isLambda
  withNaryArg 4 do
    let α ← withBindingDomain delab
    withBindingBodyUnusedName fun n => do
      let n : TSyntax `ident := ⟨n⟩
      let b ← delab
      `(∑ $n:ident : $α, $b)
-/
