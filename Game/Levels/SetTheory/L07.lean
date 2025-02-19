import Game.Metadata

World "SetTheory"
Level 7

Title "" -- "gesamte Menge"

Introduction
"
Auf der anderen Seite ist `(univ : Set ℕ)` die gesamte Teilmenge
aller Elemente aus `ℕ`.

Ist das nicht einfach `ℕ`?

Nein, `(univ : Set ℕ)` und `(ℕ : Type)` sind zwei unterschiedliche Objekte, auch
wenn sie informell das gleiche Beschreiben.
"

open Set

-- TODO: tauto kann das direkt lösen. Etwas schwierigere Aufgabe?

Statement (h : (univ : Set ℕ) ⊆ ∅) : (univ : Set ℕ) = ∅ := by
  -- simp at h
  tauto

/-- -/
DefinitionDoc Set.univ as "univ"


NewDefinition Set.univ
TheoremTab "Set"

Conclusion ""
