import Game.Metadata

World "Cartan"
Level 3


/---/
TheoremDoc Filter.inter_mem as "Filter.inter_mem"

/- Third axiom of filter. -/
Statement {α : Type*} {f : Filter α} {s t : Set α} (h : s ⊆ t) (hs : s ∈ f)
    (ht : t ∈ f) : s ∩ t ∈ f := by
  apply Filter.inter_mem hs ht

NewTheorem Filter.inter_mem
