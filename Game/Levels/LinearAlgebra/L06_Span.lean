import Game.Metadata



World "Module"
Level 6

Title "Hülle"

Introduction
"
Ein typischer Untervektorraum ist die Hülle `⟨M⟩`, oder `span`, also die Menge aller
`K`-Linearkombinationen von Elementen aus der Menge `M`.

In Lean ist dies `Submodule.span K M`.

"

local notation "ℝ²" => Fin 2 → ℝ

open Submodule Set Finsupp

-- mem_span_of_mem
/-- Zeige, dass $x \\in M$ auch Element von der $K$-linearen Hülle
  \\langle M \\rangle ist. -/
Statement {V K : Type _} [Field K] [AddCommMonoid V]
    [Module K V] (M : Set V) {x : V} (h : x ∈ M) :
    x ∈ span K M := by
  rw [mem_span]
  intro p hp
  specialize hp h
  assumption
