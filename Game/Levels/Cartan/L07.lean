import Game.Metadata

World "Cartan"
Level 7

open Filter Topology

/---/
TheoremDoc Filter.mem_inf_iff_superset as "Filter.mem_inf_iff_superset"

/---/
TheoremDoc Filter.mem_principal_self as "Filter.mem_principal_self"

/---/
TheoremDoc Set.inter_subset_inter as "Set.inter_subset_inter"

/---/
TheoremDoc subset_trans as "subset_trans"

Statement {α : Type*} {s t : Set α} :
    𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) := by
  ext x
  constructor
  · intro h
    rw [mem_inf_iff_superset] at h
    obtain ⟨u, hu, v, hv, hx⟩ := h
    rw [mem_principal] at hu hv ⊢
    apply subset_trans _ hx
    apply Set.inter_subset_inter hu hv
  · intro h
    rw [mem_inf_iff_superset]
    rw [mem_principal] at h
    use s
    constructor
    · apply mem_principal_self
    · use t
      constructor
      · apply mem_principal_self
      · assumption

NewTheorem Filter.mem_inf_iff_superset Filter.mem_principal_self Set.inter_subset_inter
  subset_trans
