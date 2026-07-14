import Game.Metadata

World "Cartan"
Level 1

Introduction "
A *filter* on a type `α` is a collection `f` of subsets of `α` — you can think of it
as a generalized notion of a set of *large* subsets. It has to satisfy three axioms:

1. the whole set is large: `Set.univ ∈ f`;
2. any superset of a large set is large: if `s ∈ f` and `s ⊆ t`, then `t ∈ f`;
3. the intersection of two large sets is large: if `s ∈ f` and `t ∈ f`, then `s ∩ t ∈ f`.

In Mathlib, these three axioms are recorded as the theorems `Filter.univ_mem`,
`Filter.mem_of_superset` and `Filter.inter_mem`. In the first three levels you
verify one axiom each — here the first one.
"


/-- A *filter* on a type `α` is a collection of subsets of `α` that contains `Set.univ`,
is upward closed, and is closed under intersection. -/
DefinitionDoc Filter as "Filter"

/---/
TheoremDoc Filter.univ_mem as "Filter.univ_mem"

/- First axiom of filter. -/
Statement {α : Type*} (f : Filter α)  : Set.univ ∈ f := by
  apply Filter.univ_mem

NewTheorem Filter.univ_mem
NewDefinition Filter
