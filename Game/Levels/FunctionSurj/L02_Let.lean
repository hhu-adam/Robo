import Game.Metadata


World "FunctionSurj"
Level 2

Title "let"

Introduction
"
Ihr macht euch auf in Richtung Bibliothek entlang kleiner Pfade zwischen verschiedensten Behausungen.

**Du**: Sag mal, ich weiß jetzt dass ich eine Funktion als `fun x ↦ x - 1` definieren kann,
aber wie kann ich ihr einen Namen geben?

**Robo**: Wenn jemand hier lokal eine Funktion definiert, werden die dir
`f : ℤ → ℤ := fun x ↦ x - 1; …` als Objekt mitgeben.

**Robo**: Im Beweis hingegen, kannst du dir mit `let f := fun (x : ℤ) ↦ x - 1` selbst eine
temporäre Definition machen.
"

open Function

--set_option pp.all true

Statement (x : ℤ) :
    let f : ℤ → ℤ := fun x ↦ x + 5
    ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 2 := by
  Hint "
    **Du**: Ist `g ∘ {f}` Komposition von Funktionen?

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
  Hint "**Robo**: gute Wahl! Jetzt kannst du diese mit `use g` benutzen."
  use g
  Hint "
    **Robo**: `({g} ∘ f) x` ist per Definition `{g} (f x)`, aber mit
    `rw [comp_apply]` kann man das explizit umschreiben, aber `simp` kennt das
    Lemma auch."
  Branch
    simp
    Hint (hidden := true) "
      **Robo**: Das sieht nach einem Fall für `ring` aus."
    ring
  rw [comp_apply]
  Hint (hidden := true) "
    **Robo**: `ring` sieht durch lokale Definitionen wie
    `{f}` und `{g}` hindurch,
    du kannst es also direkt benutzen."
  ring

/--
Sagt dass `(f ∘ g) x` das gleiche ist wie `f (g x)`.
-/
TheoremDoc Function.comp_apply as "comp_apply" in "Function"

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
