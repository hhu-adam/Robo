import Game.Metadata

World "Cartan"
Level 3

open Filter Topology

Introduction "Intro Cartan L03: another example. The *principal filter* `𝓟 s` of a set `s` if it
consists of all supersets of s."

/-
In this level you show that the principal filter of the singleton `{a}` lies below
the neighborhood filter `𝓝 a`: every neighborhood of `a` contains `{a}`.
-/

/---/
TheoremDoc Filter.le_def as "le_def" in "Filter"

/---/
TheoremDoc mem_of_mem_nhds as "mem_of_mem_nhds"

/---/
TheoremDoc principal_singleton_le_nhds as "principal_singleton_le_nhds"

/- Order relation on filters: `f ≤ g` means every member of `g` is a member of `f`. -/
Statement principal_singleton_le_nhds {a : ℝ} : 𝓟 {a} ≤ 𝓝 a := by
  Hint "Filters are ordered: `𝓕 ≤ 𝓖` means that every member of `𝓖` is also a member of `𝓕`
  (`le_def`). Note that this is the *reverse* of set inclusion — but it is chosen
so that `𝓟 s ≤ 𝓟 t` holds exactly when `s ⊆ t`."
  rw [le_def]
  intro s hs
  simp
  apply mem_of_mem_nhds
  assumption



NewTheorem Filter.le_def mem_of_mem_nhds
NewDefinition Filter.principal
