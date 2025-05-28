import Game.Metadata


World "Vieta"
Level 10

-- "A function which semiconjugates an endofunction to the successor function is surjective"
Title "" -- "Boss"
Introduction
"
Die Kampfgeräusche wirken inzwischen bedrohlich nahe.
Ihr hört deutlich vernehmbar Kanonenschüsse.
Und da saust auch schon wieder ein Pfeil an euch vorbei.

**Du**:  Ähm, sollten wir vielleicht …

**Vieta**:  Keine Sorge, für einen Aufgabe haben wir noch Zeit.
"

open Function Nat

Statement {A : Type} {f : A → ℕ} (h : ∃ a : A, f a = 0) {g : A → A}
    (hs : f ∘ g = succ ∘ f) : ∀ n, ∃ a, f a = n := by
  Hint "
    **Du**: Was ist denn hier `succ`?

    **Robo**:  `succ : ℕ → ℕ` ist die Abbildung, die eine natürliche Zahl auf ihren *successor*,
    also ihren Nachfolger, abbildet.  Mit anderen Worten:  `n ↦ n + 1`.

    **Du**: Ach so. Und von der Abbildung `f` soll ich, wenn ich das richtig lese,
    im Wesentlichen zeigen, dass sie surjektiv ist.

    **Robo**:  Sieht so aus!
  "
  Hint (hidden := true)"
  **Robo**:  Schau mal, die Abbildung geht nach `ℕ`!

  Du hebst die Augenbrauen.

  **Robo**: Könnte was mit Induktion zu tun haben.  Ich mein ja nur.
  "
  intro n
  induction n with n hn
  · assumption
  · obtain ⟨b, hb⟩ := hn
    use g b
    Branch
      rw [← hb]
      apply congr_fun hs
    Hint (hidden := true) "**Robo**: Willst du vielleicht mit `congr_fun` die Annahme `{hs}`
    zu `∀ x, ({f} ∘ {g}) x = (succ ∘ {f})` umschreiben?"
    apply congr_fun at hs
    specialize hs b
    simp at hs
    rw [hs]
    rw [hb]

Conclusion "
**Vieta**:  Bravo!  Jetzt aber nichts wie weg von hier.
Hier gehts lang.  Ich bring euch zurück zum Raumschiff.
"
NewDefinition Nat.succ
