import Game.Metadata
import Game.Levels.Quotient.L02

World "Quotient"
Level 3

open Pointwise

instance (A : FiniteSets) : Finite A := A.2

Introduction "Intro Quotient L03"

/-- Two elements of `FiniteSets` are equivalent when there is a bijection between them. -/
DefinitionDoc FiniteSets.isoSetoid as "isoSetoid" in "Quotient"

Statement FiniteSets.isoSetoid : Setoid FiniteSets := by
  Hint "[Hint q3set] A *setoid* is a type equipped with an
    equivalence relation, written `s ≈ t`. Here two finite sets should count as equivalent
    when there is a bijection between them, so the relation to supply is `Nonempty (s ≃ t)` —
    together with proofs that it is reflexive, symmetric and transitive."
  Hint (hidden := true) "[Hint q3tmpl] Give the relation and leave the three axioms for later:
    ```
    refine' \{ r s t := Nonempty (s ≃ t), ..}
    ```
    The `..` stands for the fields you have not filled in yet."
  refine' { r s t := Nonempty (s ≃ t), ..}
  constructor
  · Hint "[Hint q3refl] Reflexivity: a finite set is in bijection with itself, via the identity."
    intro x
    Hint (hidden := true) "[Hint q3ctor] `constructor` reduces the goal to actually producing
      a bijection."
    constructor
    rfl
  · Hint "[Hint q3symm] Symmetry: a bijection can be turned around."
    intro x y hxy
    Hint "[Hint q3obt] `{hxy}` only says that a bijection *exists*, so unpack it with `obtain`
      before you can invert it."
    Hint (hidden := true) "[Hint q3obth] `obtain ⟨xy⟩ := {hxy}`."
    obtain ⟨xy⟩ := hxy
    constructor
    Hint (hidden := true) "[Hint q3esym] `Equiv.symm` runs `{xy}` backwards."
    apply Equiv.symm xy
  · Hint "[Hint q3trans] Transitivity: two bijections compose to one."
    intro x y z hxy hyz
    obtain ⟨xy⟩ := hxy
    obtain ⟨yz⟩ := hyz
    constructor
    Hint (hidden := true) "[Hint q3etrn] `Equiv.trans` runs `{xy}` and then `{yz}`."
    apply Equiv.trans xy yz

NewDefinition Equiv.symm Equiv.trans
