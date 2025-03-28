import Game.Metadata


World "Vieta"
Level 6

Title "" -- "Stückweise Definition"

Introduction
"
**Vieta**:  Wir sollten doch noch mal ein Stück laufen.  Hier entlang!

Er eilt davon, und ihr folgt, so schnell ihr könnt.
Als ihr den Ort erreicht, an dem er schließlich stehen bleibt, bist du völlig außer Puste.
Vieta lacht.

**Vieta**:  Reine Vorsichtsnahme!  Ich muss ja auf meine Besucher achtgeben.
So viel Besuch bekomme ich nicht!

Er reicht euch das nächste Blatt.
"

open Set Function

Statement :
    let f : ℚ → ℚ := fun x ↦ 5 * x
    let g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0
    f ∘ g = g ∘ f := by
  Hint "
    **Robo**: Jetzt haben wir zwei Abbildungen, eine davon mit stückweiser Definition.

    **Du**: Also, ich soll zeigen, dass die beiden vertauschbar sind?

    **Robo**: Genau, am besten wählst du mit `funext x` ein beliebiges Element aus, und zeigst das
    dann für dieses."
  funext x
  Hint "
    **Du**: Ah und jetzt kann ich erst einmal `(g ∘ f) {x}` zu `g (f {x})` umschreiben?

    **Robo**: Mit `simp` klappt das."
  simp -- or simp [f, g]
  -- TODO: add `(defeq := _)` so that this triggers for `simp [f, g]` too
  Hint (strict := true) "
    **Robo**: Jetzt kannst du nämlich eine Fallunterscheidung
    machen, `by_cases h : 0 ≤ {x}`.

    **Du**: Damit krieg ich die Fälle `0 ≤ {x}` und `0 > {x}`?

    **Robo**: Genau! Oder präziser `0 ≤ {x}` und `¬(0 ≤ {x})`. Das ist nicht ganz das gleiche,
    und man könnte mit dem Lemma `not_le` zwischen `¬(0 ≤ {x})` und `0 > {x}` wechseln."
  by_cases h : 0 ≤ x
  · Hint "**Du**: Jetzt muss ich wohl doch mal die Definitionen benutzen.

    **Robo**: Dann benutz sie mal `simp [f, g]`!"
    simp [f, g]
    Hint "
      **Robo**: Jetzt hast du `rw [if_pos {h}]` zur Verfügung, um das if-then-else zu
      reduzieren."
    rw [if_pos h, if_pos h]
    ring
  · Hint (hidden := true) "**Robo**: Nochmals `simp [f, g]`."
    simp [f, g]
    Hint "**Du**: Ah, und die Verneinung von `if_pos` ist sicher …"
    Hint (hidden := true) "**Robo**: `if_neg`, genau!"
    rw [if_neg h, if_neg h]

Conclusion""

/---/
TheoremDoc if_neg as "if_neg" in "Logic"

/---/
TheoremDoc if_pos as "if_pos" in "Logic"

NewTheorem if_pos if_neg
TheoremTab "Logic"
