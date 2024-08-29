import Game.Metadata
import Game.Levels.SetTheory.L04_SubsetEmpty


World "SetTheory"
Level 5

Title "Empty"

Introduction
"
**Robo**: Ist das denn wirklich so wichtig?

**Verkäufer**: Hier, beantworte mir doch mal folgendes.
"

open Set Subset

/---/
TheoremDoc Set.eq_empty_iff_forall_not_mem as "eq_empty_iff_forall_not_mem" in "Set"

Statement Set.eq_empty_iff_forall_not_mem {A : Type _} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  Branch
    -- User solution by Yagub A.
    constructor
    · intro h
      rw [h]
      tauto
    · intro h
      by_contra h0
      rw [Subset.antisymm_iff] at h0
      rw [not_and_or] at h0
      obtain h8 | h8 := h0
      · rw [subset_def] at h8
        rw [not_forall] at h8
        Hint (hidden := true) "jetzt könntest du {h8} mit `obtain` aufteilen"
        obtain ⟨x, hx⟩ := h8
        apply hx
        intro hxs
        have hxs2 := h x
        contradiction
      · rw [subset_def] at h8
        rw [not_forall] at h8
        obtain ⟨x, hx⟩ := h8
        apply hx
        intro hxs
        have hxs2 := h x
        contradiction
  rw [←subset_empty_iff]
  Branch
    rfl -- This is quite a miracle :)
  trivial

NewTheorem Set.subset_empty_iff
TheoremTab "Set"
