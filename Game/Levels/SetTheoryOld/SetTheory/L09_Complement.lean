import Game.Metadata
import Game.Levels.SetTheory.L08_UnionInter


World "SetTheory"
Level 9

Title "Komplement"

Introduction
"
**Dame**: Ok gut. Aber hier nochmals was, was ich in der Zeitung gelesen habe:
"

open Set

/--  -/
Statement (A : Set ℕ) (h : Aᶜ ⊆ A) : A = univ := by
  Hint "**Du**: Gleichheit von Mengen. Das ist sicher wieder ein Fall für beide
  Inklusionen.

  **Robo**: Das war `Subset.antisymm_iff`.

  "
  rw [Subset.antisymm_iff]
  constructor
  · Hint (hidden := true) "**Robo**: `⊆ univ` ist ein Fall für `simp`."
    simp
  · Hint (hidden := true) "Da `⊆` als `∀x, x ∈ A → x ∈ B ` definiert ist, fängst du
    am besten mit `intro` an."
    intro x _hx
    Hint "Eine Möglichkeit ist, eine Fallunterscheidung zu machen: `by_cases g: {x} ∈ {A}ᶜ`."
    by_cases h4 : x ∈ Aᶜ
    · Hint "Hier könnte `mem_of_subset_of_mem` hilfreich werden."

      rw [mem_compl_iff] at h4
      apply mem_of_subset_of_mem h
      assumption
    · Hint "Diese Richtung geben wir als Lemma: `not_mem_compl_iff`."
      rw [not_mem_compl_iff] at h4
      assumption

NewTheorem Set.mem_compl_iff Set.not_mem_compl_iff Set.mem_of_subset_of_mem
DisabledTactic tauto
TheoremTab "Set"
