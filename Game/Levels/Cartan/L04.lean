import Game.Metadata

World "Cartan"
Level 4

open Filter Topology

Introduction "
The *principal filter* `𝓟 s` of a set `s` is the simplest filter one can build:
it consists of all supersets of `s` — a set is 'large' precisely when it contains `s`.

Filters are ordered: `f ≤ g` means that every member of `g` is also a member of `f`
(`Filter.le_def`). Note that this is the *reverse* of set inclusion — but it is chosen
so that `𝓟 s ≤ 𝓟 t` holds exactly when `s ⊆ t`.
"

/-
In this level you show that the principal filter of the singleton `{a}` lies below
the neighborhood filter `𝓝 a`: every neighborhood of `a` contains `{a}`.
-/

/-- The *principal filter* `𝓟 s` of a set `s` consists of all sets containing `s`. -/
DefinitionDoc Filter.principal as "𝓟"

/---/
TheoremDoc Filter.le_def as "Filter.le_def"

/---/
TheoremDoc Filter.mem_principal as "Filter.mem_principal"

/---/
TheoremDoc Set.singleton_subset_iff as "Set.singleton_subset_iff"

/---/
TheoremDoc principal_singleton_le_nhds as "principal_singleton_le_nhds"

/- Order relation on filters: `f ≤ g` means every member of `g` is a member of `f`. -/
Statement principal_singleton_le_nhds {a : ℝ} : 𝓟 {a} ≤ 𝓝 a := by
  rw [le_def]
  intro s hs
  rw [mem_principal]
  rw [Set.singleton_subset_iff]
  apply mem_of_mem_nhds
  assumption

/- Note that the `≤` in `Filter` is the reverse direction of the `≤` in `Set`. -/

NewTheorem Filter.le_def Filter.mem_principal Set.singleton_subset_iff
NewDefinition Filter.principal
