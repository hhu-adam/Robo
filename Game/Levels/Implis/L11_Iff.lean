import Game.Metadata

World "Implis"
Level 11

Title "" -- "Genau dann wenn"

/-
Introduction
"
**Operationsleiter**: Ah, die nächste Seite ist auch von diesem Kollegen.
Aber da ist noch eine Notiz bei. Wir hatten hierfür schon einmal einen Beweis,
aber den mochte er nicht. Er wollte einen Beweis, der weder `rw` noch `apply` verwendet!!

Er holt tief Luft und seufzt.

**Operationsleiter**: Ich glaube, der stellt sich immer viel dümmer, als er ist.
Aber meint Ihr, Ihr schafft das?
"
-/
Introduction "Intro Implis L11: Prove without using `rw` or `apply`"

Statement (A B : Prop) : (A ↔ B) → (A → B) := by
  -- Hint "**Du**: Hmm, mindestens mit der Implikation kann ich anfangen."
  Hint "Start with implication"
  -- Hint (hidden := true) "**Robo**: Genau, das war `intro`."
  Hint (hidden := true) "Try `intro`"
  intro h
  /-
  Hint "
    **Du**: Also, ich kenne `rw [{h}]` und `apply ({h}.mp)`, aber das wollten wir ja
    diesmal vermeiden.

    **Robo**: Was du machen könntest, ist, mit `obtain ⟨mp, mpr⟩ := {h}` die Annahme
    in zwei Teile aufteilen."
  -/
  Hint "Instead of `rw [{h}]` and `apply ({h}.mp)` try `obtain ⟨mp, mpr⟩ := {h}`"
  Branch
    intro
    /-
    Hint "
      **Robo**: Hier müsstest du jetzt `rw [←{h}]` oder `apply {h}.mp` benutzen.
      Geh lieber einen Schritt zurück, sodass das Goal `A → B` ist."
    -/
    Hint "Try `rw [←{h}]` | `apply {h}.mp`. Go step back s.t. goal `A → B`"
  obtain ⟨mp, _mpr⟩ := h
  -- Hint (hidden := true) "**Du**: Ah, und jetzt ist das Beweisziel in den Annahmen."
  Hint (hidden := true) "Goal is in assumptions"
  assumption

/-
Conclusion
"
**Operationsleiter**: Perfekt, das sollte reichen!
"
-/
Conclusion "`CONC` Conclusion Implis L11"

OnlyTactic intro obtain assumption
DisabledTactic rw apply tauto
