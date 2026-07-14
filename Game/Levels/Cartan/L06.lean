import Game.Metadata

World "Cartan"
Level 6

open Filter Topology

/---/
TheoremDoc Filter.mem_sup as "Filter.mem_sup"

/---/
TheoremDoc Set.union_subset as "Set.union_subset"

/---/
TheoremDoc Set.union_subset_iff as "Set.union_subset_iff"

Statement {α : Type*} {s t : Set α} :
    𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) := by
  ext x
  constructor
  · intro h
    rw [mem_sup] at h
    obtain ⟨hs, ht⟩ := h
    rw [mem_principal] at hs ht ⊢
    apply Set.union_subset hs ht
  · intro h
    rw [mem_sup]
    simp [mem_principal] at h ⊢
    apply Set.union_subset_iff.mp
    assumption

NewTheorem Filter.mem_sup Set.union_subset Set.union_subset_iff
