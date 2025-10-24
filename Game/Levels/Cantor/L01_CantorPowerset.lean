import Game.Metadata

World "Cantor"
Level 1

Title "" -- "Cantor's Diagonalargument"

/-
Introduction
"
**Cantor**: … Wir betrachten also eine Abbildung `f` von `A` in die Potenzmenge von `A`,
und nun die Menge alle jener Elemente aus `A`, die nicht in ihrem Bild unter `f` liegen …

Oh!  Ein Publikum. Nein, *zwei* Publikums!  Hört und seht, seht und staunt.

Er zieht aus seinem Zylinder einen Zettel, faltet ihn zu einer Schwalbe,
und lässt ihn zu euch herunterfliegen.

**Cantor**:  Wenn ich schon zwei Publikums habe, könnten die ja auch ein bisschen mitmachen, nicht wahr?
"
-/
Introduction "Intro Cantor L01: Mapping `f` from `A` to the power set of `A`"

Conclusion ""

open Set Function

Statement {A : Type} (f : A → Set A) : ¬ ∃ (a : A), f a = { x | x ∉ f x } := by
  --Hint "**Robo**: Denk daran, dass `mem_setOf` aus `Set` irgendwann hilfreich sein wird."
  /-
  Hint "**Du**:  Ist also `Set A` die Potenzmenge von `A`?

  **Robo**: Ja, sozusagen.  Es ist die Menge, oder genauer der Typ, aller Teilmengen von `A`.

  **Du**:  Und ich soll zeigen, dass … aha.  Vermutlich ein Widerspruchsbeweis, oder?

  **Robo**:  Vermutlich.
  "
  -/
  Hint "Comment"
  Branch
    push_neg
    intro _a
    by_contra _ha
  by_contra h
  /- Hint "**Cantor**:  Ja, ja, ja!  Und jetzt hübsch `{h}` zerlegen …" -/
  /- Hint (hidden := true)"**Robo:  … mit `obtain`, wie immer." -/
  Hint (hidden := true) "Try `obtain`"
  obtain ⟨a, ha⟩ := h
  /- Hint (strict := true) "**Du**: Jetzt vermutlich eine Fallunterscheidung zu `{a} ∈ {f} {a}`?" -/
  Hint (strict := true) "Comment"
  /- Hint (hidden := true) (strict := true) "**Robo**: Das wäre `by_cases h₁ : {a} ∈ {f} {a}`." -/
  Hint (hidden := true) (strict := true) "Try `by_cases h₁ : {a} ∈ {f} {a}`"
  by_cases h₁ : a ∈ f a
  /-
  Hint "Cantor reibt sich die Hände.

    **Cantor**:  Das sieht gut aus!
    "
  -/
  Hint "Comment"
  · Branch
      rw [ha] at h₁
      /-
      Hint "
        **Cantor**: Gute Idee!  Fast richtig!
        Aber ihr werdet die ursprünglich Annahme
        `{h₁} : {a} ∈ {f} {a}` gleich noch einmal brauchen.

        **Robo**:  Okay, zurück und mit `have` weiter.
        Oder mit `suffices : {a} ∉ {f} {a}`!
        "
      -/
      Hint "Try `have` | `suffices : {a} ∉ {f} {a}`"
    suffices : a ∉ f a
    · contradiction
    rw [ha] at h₁
    simp at h₁ --or: rw [mem_setOf] at h₁
    assumption
  · apply h₁
    rw [ha]
    simp --or: rw [mem_setOf]
    assumption

TheoremTab "Set"

/-
Conclusion "Cantor klatsch in die Hände und freut sich.
Wie von Zauberhand fliegt der Zettel zu ihm zurück."
-/

Conclusion "`CONC` Conclusion Cantor L01"
