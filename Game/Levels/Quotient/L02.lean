import Game.Metadata
import Game.Levels.Quotient.L01

World "Quotient"
Level 2

Introduction "Intro Quotient L02"

def FiniteSets : Type 1 := { A : Type // Finite A }

/-- Treat an element of `FiniteSets` as the type it bundles. -/
instance : CoeSort FiniteSets Type := ⟨Subtype.val⟩

Statement (A : FiniteSets) : Finite A := by
  Hint "[Hint q2bdl] An element of `FiniteSets` is a *bundle*: a type together with a proof
    that this type is finite. Writing `A` where a type is expected picks out the first
    component."
  Hint (hidden := true) "[Hint q2snd] That second component is `A.2`."
  apply A.2
