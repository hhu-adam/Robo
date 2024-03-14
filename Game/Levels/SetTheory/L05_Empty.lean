import Game.Metadata
import Game.Levels.SetTheory.L04_SubsetEmpty


World "SetTheory"
Level 5

Title "Empty"

Introduction
"
Zeige folgendes Lemma, welches wir gleich brauchen werden:
"

open Set

Statement Set.eq_empty_iff_forall_not_mem {A : Type _} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  Hint "Das Lemma `subset_empty_iff` von letzter Aufgabe könnte hilfreich sein."
  Branch
    -- User solution by Yagub A.
    constructor
    · intro h
      rw[h]
      tauto
    · intro h
      by_contra h0
      rw[Subset.antisymm_iff] at h0
      rw[not_and_or] at h0
      rcases h0 with h8 | h8
      · rw[subset_def] at h8
        rw[not_forall] at h8
        Hint (hidden := true) "jetzt könntest du {h8} mit `rcases` aufteilen"
        rcases h8 with ⟨x, hx⟩
        apply hx
        intro hxs
        have hxs2 := h x
        contradiction
      · rw[subset_def] at h8
        rw[not_forall] at h8
        rcases h8 with ⟨x, hx⟩
        apply hx
        intro hxs
        have hxs2 := h x
        contradiction
  rw [←subset_empty_iff]
  rfl -- This is quite a miracle :)

NewTheorem Set.subset_empty_iff
TheoremTab "Set"
