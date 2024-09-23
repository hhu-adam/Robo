import Game.Metadata


World "Function"
Level 9

-- "A function which semiconjugates an endofunction to the successor function is surjective"
Title "Boss"
Introduction
"
"

open Function Nat

Statement {A : Type} {f : A → ℕ} (h : ∃ a : A, f a = 0) {g : A → A}
    (hs : f ∘ g = succ ∘ f) (n : ℕ) : ∃ a, f a = n := by
  Hint "
  **Du**: Diese Aufgabe sagt, mehrheitlich dass eine Funktion `f` in die natürlichen
  Zahlen surjektiv ist, falls die `0` im Bild liegt und es einen
  Endomorphismus `g : A → A` gibt, sodass `f ∘ g` das gleiche ist wie, `succ ∘ f`.

  **Robo*: Im Fachjargon sagt man \"`f` semikonjugiert `g` zu `succ`\".

  **Du**: Ich glaube, einen Beweis den ich kenne startet mit Induktion über `n`
  "
  induction n with n hn
  · assumption
  · obtain ⟨b, hb⟩ := hn

    use g b
    Branch
      rw [← hb]
      apply congr_fun hs
    Hint (hidden := true) "**Robo**: Willst du vielleicht `{hs}`
    zu `∀ x, ({f} ∘ {g}) x = (succ ∘ {f})` umschreiben?"
    apply congr_fun at hs
    -- Note: Leave this as the main branch, so that the planet is registered
    -- to require `have`!
    have hs := hs b
    simp at hs
    rw [hs]
    rw [hb]
