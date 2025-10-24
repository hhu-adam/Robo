import Game.Metadata


World "Vieta"
Level 4

Title "" -- "let"

/-
Introduction
"
**Vieta**:  Jetzt müssen wir mal ein Stück hier rüber gehen.

Er schiebt euch vorsichtig ein paar Meter weiter.  Einen Moment später gehen an dem Ort,
an dem ihr eben gestanden habt, drei Pfeile nieder und bleiben im Boden stecken.

**Vieta**: Ganz ruhig, ich kenne mich hier aus.  Hier, ich habe noch mehr für euch.
"
-/
Introduction "`INTRO` Intro Vieta L04"

open Function

Statement (x : ℤ) :
    let f : ℤ → ℤ := fun x ↦ x + 5
    ∃ (g : ℤ → ℤ), (g ∘ f) x = x + 2 := by
  /-
  Hint "
    **Du**: Ist `g ∘ {f}` Komposition von Abbildungen?

    **Robo**: Richtig! Das schreibt man mit `\\comp`.

    **Du** Und hier könnte ich also wieder
    `let g : ℤ → ℤ := fun x ↦ _` definieren?

    **Robo**:  Ja, oder sogar  direkt `use fun (x : ℤ) ↦ _`?"
  -/
  Hint "Composition `g ∘ {f}` can be written with `\\comp`. Try `let g : ℤ → ℤ := fun x ↦ _` or `use fun (x : ℤ) ↦ _`"
  Branch
    let g : ℤ → ℤ := fun x ↦ x - 3
    -- Hint "**Robo**: Jetzt kannst du diese mit `use {g}` benutzen."
    Hint "Try `use {g}`"
    use g
    /-
    Hint "
    **Robo**: `({g} ∘ {f}) x` ist per Definition `{g} ({f} x)`. `simp` würde dieses
    Lemma auch kennen, aber mach das hier mal direkt mit `rw [comp_apply]`."
    -/
    Hint "Explain `({g} ∘ {f}) x` defined as `{g} ({f} x)`. Try `simp` | `rw [comp_apply]`"
    /-
    Hint "
    **Robo**: `ring` sieht durch lokale Definitionen wie
    `{f}` und `{g}` hindurch,
    du kannst es also direkt benutzen."
    -/
    Hint "Try `ring`, as it sees through definitions `{f}` and `{g}`"
  use fun (x : ℤ) ↦ x - 3
  /-
  Hint "
  **Robo**: `(g ∘ {f}) x` ist per Definition `g ({f} x)`. `simp` würde dieses
  Lemma auch kennen, aber mach das hier mal direkt mit `rw [comp_apply]`."
  -/
  Hint "Explain `(g ∘ {f}) x` defined as `g ({f} x)`. Try `simp` | `rw [comp_apply]`"
  rw [comp_apply]
  /-
  Hint "
  **Robo**: `ring` sieht durch lokale Definitionen wie
  `{f}` hindurch,
  du kannst es also direkt benutzen."
  -/
  Hint "Try `ring` as it sees through defintion `{f}`"
  ring

/--
Sagt dass `(f ∘ g) x` das gleiche ist wie `f (g x)`.
-/
TheoremDoc Function.comp_apply as "comp_apply" in "Function"

NewTheorem Function.comp_apply
DisabledTactic simp -- simp_rw
TheoremTab "Function"

-- Conclusion ""
Conclusion "Conclusion Vieta L04"
