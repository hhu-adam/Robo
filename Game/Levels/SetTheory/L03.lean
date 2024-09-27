import Game.Metadata

World "SetTheory"
Level 3

Title "Teilmengen"

Introduction
"
Teilmengen `A ⊆ B` sind ebenfalls nur Logik.
"

open Set

Statement {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  -- Hint: do this for understanding the def!
  Hint "Zum besseren Verständnis kannst du mal `simp [subset_def] at *`
  eingeben um zu sehen, wie `⊆` definiert ist."
  simp [subset_def] at *
  Hint "Wie du siehst ist die Definition von `{A} ⊆ {B}` durch `∀ x ∈ {A}, x ∈ {B}`
    definiert, was kurz für `∀ x : ℕ, x ∈ {A} → x ∈ {B}` ist,
    weshalb `tauto` diese Logik-Aussagen auch verwenden kann."
  tauto

/-- -/
DefinitionDoc Subset as "⊆"

NewDefinition Subset
NewTheorem Set.subset_def
TheoremTab "Set"

Conclusion ""
