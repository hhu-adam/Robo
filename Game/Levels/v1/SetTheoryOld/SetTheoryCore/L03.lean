import Game.MetaData

World "SetTheoryCore"
Level 3

Title "" -- "Teilmengen"

Introduction
"
Ihr bemerkt, dass mit dem Jungen noch zwei andere
Kinder zuhörten. Eines der beiden Mädchen hat ebenfalls eine Frage.
"

-- Hat man zwei Mengen `(A B : Set ℕ)` kann man fragen, ob diese Teilmengen
-- voneinander sind: `A ⊆ B` (`\\sub`/`\\ss`) ist die Notation für Teilmengen, die auch gleich
-- sein können.

-- `A ⊆ B` ist als `∀ x, x ∈ A → x ∈ B` definiert, das heisst, ein `⊆` kann immer auch mit `intro x hx`
-- angegangen werden.

open Set

--#check Set.subset_def
--#check Subset.trans

Statement {A B C : Set ℕ} (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  Branch
    intro x hx
    apply h₂
    apply h₁
    assumption
  tauto
