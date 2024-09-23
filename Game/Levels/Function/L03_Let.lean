import Game.Metadata


World "Function"
Level 3

Title "let"

Introduction
"
**Du**: Kannst du mir nochmals eine Aufgabe stellen, Robo?
"

open Function

Statement (x : ℤ) :
    let f : ℤ → ℤ := fun x ↦ x + 5
    ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 2 := by
  Hint "
    **Du**: Ist `g ∘ {f}` Komposition von Funktionen?

    **Robo**: Richtig! Das schreibt man mit `\\comp`.

    **Du** Und hier könnte ich also wieder
    `let g := fun (x : ℤ) ↦ _` definieren oder direkt
    `use fun (x : ℤ) ↦ _`?

    **Robo**: Genau!"
  Branch
    let g := fun (x : ℤ) ↦ x - 3
    Hint "**Robo**: Jetzt kannst du diese mit `use {g}` benutzen."
    use g
    Hint "
    **Robo**: `({g} ∘ {f}) x` ist per Definition `{g} ({f} x)`. `simp` würde dieses
    Lemma auch kennen, aber mach das hier mal direkt mit `rw [comp_apply]`."
    Hint "
    **Robo**: `ring` sieht durch lokale Definitionen wie
    `{f}` und `{g}` hindurch,
    du kannst es also direkt benutzen."
  use fun (x : ℤ) ↦ x - 3
  Hint "
  **Robo**: `(g ∘ {f}) x` ist per Definition `g ({f} x)`. `simp` würde dieses
  Lemma auch kennen, aber mach das hier mal direkt mit `rw [comp_apply]`."
  rw [comp_apply]
  Hint "
  **Robo**: `ring` sieht durch lokale Definitionen wie
  `{f}` hindurch,
  du kannst es also direkt benutzen."
  ring

/--
Sagt dass `(f ∘ g) x` das gleiche ist wie `f (g x)`.
-/
TheoremDoc Function.comp_apply as "comp_apply" in "Function"

NewTheorem Function.comp_apply
DisabledTactic simp simp_rw
TheoremTab "Function"

Conclusion
"
**Du**: Dann verstehst du etwas Mathe?

**Robo**: Ich hatte ja keine Ahnung ob die generierte Aufgabe beweisbar ist… aber offenbar
hatte ich Glück.

Und damit erreicht ihr den Hügel mit der Bibliothek.
"
