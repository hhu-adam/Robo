import Game.Metadata



World "Function"
Level 2

Title "let"

Introduction
"
Ihr macht euch auf Richtung Bibliothek entlang kleiner Pfade zwischen verschiedenster Behausungen.

**Du**: Sag mal, ich weiss jetzt dass ich eine Funktion als `fun x ↦ x - 1` definieren kann,
aber wie kann ich der einen Namen geben?

**Robo**: Wenn jemand hier lokal eine Funktion definiert, werden die dir
`let f := fun (x : ℤ) ↦ x - 1; …` vor die Aussage schreiben.

**Robo**: Im Beweis hingegen, kannst du mit `let f := fun (x : ℤ) ↦ x - 1` dir selbst eine
temporäre Definition machen.

**Du**: Ohne `;`?

**Robo**: Ja, hier im Beweis ist das `;` nicht nötig weil du ja einen Schritt nach dem anderen
auf neue Zeilen schreibst. Komm, ich mache dir einmal ein Beispiel:
"

open Function

Statement (x : ℤ) :
    let f : ℤ → ℤ := fun x ↦ x + 4
    ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 1 := by
  Hint "
    **Du**: Das sieht etwas unleserlich aus, wieso steht das `f` nicht bei den Annahmen oben?

    **Robo**: Mit `intro f` kannst du genau das erreichen!"
  intro f
  Hint "
    **Du**: Das sieht schon viel besser aus!
    Ist `g ∘ {f}` Komposition von Funktionen?

    **Robo**: Richtig! Das schreibt man mit `\\comp`.

    **Du** Und hier könnte ich also zuerst
    `let g := fun (x : ℤ) ↦ _` definieren, anstatt direkt
    `use fun (x : ℤ) ↦ _`?

    **Robo**: Genau! Das ist zwar praktisch das gleiche, aber kann manchmal nützlich sein."
  Branch
    use fun (x : ℤ) ↦ x - 3
    Hint "
      **Robo**: `((fun (x : ℤ) ↦ x - 3) ∘ f) x` ist per Definition `(fun (x : ℤ) ↦ x - 3) (f x)`,
      aber mit `rw [comp_apply]` kann man das explizit umschreiben, aber `simp` kennt das
      Lemma auch."
  let g := fun (x : ℤ) ↦ x - 3
  Hint "**Robo**: gute Wahl! Jetzt kannst du diese mit `use g` benützen."
  use g
  Hint "
    **Robo**: `({g} ∘ f) x` ist per Definition `{g} (f x)`, aber mit
    `rw [comp_apply]` kann man das explizit umschreiben, aber `simp` kennt das
    Lemma auch."
  Branch
    simp
  rw [comp_apply]
  Hint "
    **Robo**: Wie schon gehabt hat `ring` Schwierigkeiten, Definitionen zu öffnen.
    Du kannst mit `unfold f` oder `rw [f]` nachhelfen."
  ring

NewTactic «let»
NewTheorem Function.comp_apply
TheoremTab "Function"

Conclusion
"
**Du**: Dann verstehst du etwas Mathe?

**Robo**: Ich hatte ja keine Ahnung ob die generierte Aufgabe beweisbar ist… aber offenbar
hatte ich Glück.

Und damit erreicht ihr den Hügel mit der Bibliothek.
"
