import Game.Metadata

World "Cartan"
Level 1

open Filter Topology

Introduction "
In this world you will meet *filters*. Formally, a filter on a type `α` is a
collection `f` of subsets of `α` satisfying three axioms:

1. `Set.univ ∈ f`;
2. if `s ∈ f` and `s ⊆ t`, then `t ∈ f`;
3. if `s ∈ f` and `t ∈ f`, then `s ∩ t ∈ f`.

In Mathlib the three axioms are the theorems `Filter.univ_mem`,
`Filter.mem_of_superset` and `Filter.inter_mem`.

An intuition is to think
of a filter as a *generalized point*: `f` collects all the sets that contain
this would-be point. The main example for us is the *neighborhood filter*
`𝓝 a` of a real number `a : ℝ`: it consists of all sets that contain every
number sufficiently close to `a`, and so describes the point `a` together with
its immediate surroundings.

In this level you prove that the intersection of two neighborhoods of `a` is
still a neighborhood of `a`.
"

/-- A *filter* on a type `α` is a collection of subsets of `α` that contains `Set.univ`,
is upward closed, and is closed under intersection. -/
DefinitionDoc Filter as "Filter"

/-- `𝓝 a` is the *neighborhood filter* of `a`: it consists of all open sets containing `a`. -/
DefinitionDoc nhds as "𝓝"

/---/
TheoremDoc Filter.univ_mem as "Filter.univ_mem"

/---/
TheoremDoc Filter.mem_of_superset as "Filter.mem_of_superset"

/---/
TheoremDoc Filter.inter_mem as "Filter.inter_mem"

/- Third axiom of filter, for the neighborhood filter. -/
Statement {a : ℝ} {s t : Set ℝ} (hs : s ∈ 𝓝 a) (ht : t ∈ 𝓝 a) :
    s ∩ t ∈ 𝓝 a := by
  Hint "[Hint zmbq] `𝓝 {a}` is a filter, so this is an instance of the third filter
  axiom, recorded in Mathlib as `Filter.inter_mem`. "
  apply Filter.inter_mem hs ht

NewTheorem Filter.univ_mem Filter.mem_of_superset Filter.inter_mem
NewDefinition Filter nhds
