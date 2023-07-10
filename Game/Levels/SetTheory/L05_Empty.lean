import Game.Metadata
import Game.Levels.SetTheory.L04_SubsetEmpty

import Game.Options.MathlibPart

set_option tactic.hygienic false

World "SetTheory"
Level 5

Title "Empty"

Introduction
"
Zeige folgendes Lemma, welches wir gleich brauchen werden:
"

open Set


Statement Set.eq_empty_iff_forall_not_mem
""
    {A : Type _} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  Hint "Das Lemma `subset_empty_iff` von letzter Aufgabe könnte hilfreich sein."
  rw [←subset_empty_iff]
  rfl -- This is quite a miracle :)

NewLemma Set.subset_empty_iff
LemmaTab "Set"
