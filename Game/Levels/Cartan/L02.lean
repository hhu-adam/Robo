import Game.Metadata

World "Cartan"
Level 2


/---/
TheoremDoc Filter.mem_of_superset as "Filter.mem_of_superset"

/- Second axiom of filter. -/
Statement {α : Type*} {f : Filter α} {s t : Set α} (h : s ⊆ t) (hs : s ∈ f) :
    t ∈ f := by
  apply Filter.mem_of_superset hs h

NewTheorem Filter.mem_of_superset
