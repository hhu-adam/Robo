import Game.Metadata

namespace Nat

World "Prado"
Level 1

Title "Teilbarkeit"

Introduction
"
**Du**: Wie schreib ich denn, \"`a` teilt `b`\"?

**Robo**: Als `a ∣ b`, aber der senkrechte Strich ist
  ein spezieller, den man mit `\\|` oder `\\dvd` schreibt.
"

Statement dvd_add {a b c : ℕ} (h : a ∣ b) (g : a ∣ c) : a ∣ b + c := by
  Hint "
  **Robo**: Definiert ist dieses Symbol als `∃ k, b = a * k`.

  **Du**: Dann kann ich direkt `obtain` und `use` verwenden, wie wenn es ein `∃` wäre?

  **Robo**: Genau!"
  Hint (hidden := true) "**Robo**: Fang doch damit an, mit `obtain ⟨x ,hx⟩ := _`
  alle Hyptothesen aufzuteilen."
  obtain ⟨x, h⟩ := h
  obtain ⟨y, g⟩ := g
  Hint (hidden := true) "**Robo**: Jetzt musst du mit `use _` eine Zahl angeben so dass
  `{b} + {c} = {a} * _` gilt."
  use x + y
  Hint (hidden := true) "**Du**: Mit ein bisschen umschreiben kann man sicer `ring` verwenden."
  rw [h, g]
  ring

/--
`a ∣ b` bedeutet `∃ k, b = a * k`.

**Warnung**: Die Symbole `∣` (`\\dvd`) und `|` (ASCII vertikaler Strich) sind zwei unterschiedliche
Zeichen! Das erste wird ausschliesslich für "geteilt" verwendet, das andere kommt zum Beispiel im
Syntax `obtain h₁ | h₂ := h` vor.
-/
DefinitionDoc Dvd.dvd as "· ∣ ·"

NewDefinition Dvd.dvd
TheoremTab "Nat"
