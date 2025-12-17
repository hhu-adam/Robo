import Game.Metadata
import Game.Levels.Prado.L01_prime_two

World "Prado"
Level 2

Title ""

/-
Introduction
"
**Du** *(flüsternd)*: Robo, meinst du, wir sollen es ihm sagen?

**Robo**: Dass `2` die einzige gerade Primzahl ist?
Er wird es nicht glauben wollen, solange wir ihm keinen Beweis präsentieren.

**Du**:  Und meinst du nicht, wir können das zeigen?  Du kennst doch die Sprache.
Lass uns mal probieren.  Wie schreib ich zum Beispiel „`a` teilt `b`“?

**Robo**: Na schön. Also  „`a` teilt `b`“ schreibst du als `a ∣ b`, wobei du den senkrechten Strich
  als `\\|` oder `\\dvd` schreiben musst.  Probier zum Beispiel mal diese Aufgabe hier.
"
-/
Introduction "Intro Prado L02: Prove that `2` is only even prime by using the expression „`a` divides `b`“.
„`a` divides `b`“ is written as `a ∣ b`, where the vertical bar can be either written as `\\|` or `\\dvd`
"

-- This is `Nat.dvd_add`, but currently that statement is not needed anywhere.
-- /---/
--TheoremDoc Nat.dvd_add as "dvd_add" in "ℕ"

namespace Nat

Statement {a b c : ℕ} (h : a ∣ b) (g : a ∣ c) : a ∣ b + c := by
  /-
  Hint "
  **Robo**: Definiert ist `a ∣ b` natürlich als `∃ k, b = a * k`.
  Am besten schreibst du das für den Anfang überall explizit aus:
  ```
  rw [dvd_iff_exists_eq_mul_left] at *
  ```
  "
  -/
  Hint "`a ∣ b` is defined as `∃ k, b = a * k`. State is explicitly with
  ```
  rw [dvd_iff_exists_eq_mul_left] at *
  ```
  "
  rw [dvd_iff_exists_eq_mul_left] at * -- optional
  /-
  Hint (hidden := true) "
    **Du**:  Und jetzt mache ich mit `obtain` und `use` weiter?

    **Robo**: Genau.  Als nächstes nimmst du die Annahmen mit `obtain ⟨x ,hx⟩ := _`
  usw. auseinander."
  -/
  Hint "Continue with `obtain` and `use`. Fristly diect assumptions with `obtain ⟨x ,hx⟩ := _`"
  obtain ⟨x, h⟩ := h
  obtain ⟨y, g⟩ := g
  -- Hint (hidden := true) "**Robo**: Jetzt musst du mit `use _` eine Zahl angeben, sodass
  -- `{b} + {c} = {a} * _` gilt."
  Hint (hidden := true) "Try `use _` such that `{b} + {c} = {a} * _`"
  use x + y
  -- Hint (hidden := true) "**Robo**: Mit ein bisschen umschreiben kann man sicher `ring` verwenden."
  Hint (hidden := true) "Rewrite so you can use `ring`"
  rw [h, g]
  Branch
    linarith  -- works here, but omega does not!
  ring

/--
`a ∣ b` bedeutet `∃ k, b = a * k`.

**Warnung**: Die Symbole `∣` (`\\dvd`) und `|` (ASCII vertikaler Strich) sind zwei unterschiedliche
Zeichen! Das erste wird ausschließlich für „teilt“ verwendet, das andere kommt zum Beispiel in der
Syntax `obtain h₁ | h₂ := h` vor.
-/
DefinitionDoc Dvd.dvd as "· ∣ ·"

NewDefinition Dvd.dvd

/---/
TheoremDoc dvd_iff_exists_eq_mul_left as "dvd_iff_exists_eq_mul_left" in "ℕ"
NewTheorem dvd_iff_exists_eq_mul_left

TheoremTab "ℕ"

/-
Conclusion "**Guino**:  Was flüstert ihr denn da?

**Du**:  Ach, nichts.  Robo versucht mich nur daran zu erinnern, was genau eine Primzahl ist.

Guino schaut sich euern Beweis an.

**Guino**: Nicht schlecht, nicht schlecht.  Aber lasst uns doch ein bisschen weitergehen.
Das Museum ist zwar noch leer, aber fertig.  Und es ist wirklich gut geworden.  Schaut mal, hier entlang!
"
-/
Conclusion "Conclusion Prado L02"
