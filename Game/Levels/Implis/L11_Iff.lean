import Game.Metadata

World "Implis"
Level 11

Title "" -- "Genau dann wenn"

Introduction
"
**Operationsleiter**: Ah, die nächste Seite ist auch von diesem Kollegen.
Aber da ist noch eine Notiz bei. Wir hatten hierfür schon einmal einen Beweis,
aber den mochte er nicht. Er wollte einen Beweis, der weder `rw` noch `apply` verwendet!!

Er holt tief Luft und seufzt.

**Operationsleiter**: Ich glaube, der stellt sich immer viel dümmer, als er ist.
Aber meint Ihr, Ihr schafft das?
"

Statement (A B : Prop) : (A ↔ B) → (A → B) := by
  Hint "**Du**: Hmm, mindestens mit der Implikation kann ich anfangen."
  Hint (hidden := true) "**Robo**: Genau, das war `intro`."
  intro h
  Hint "
    **Du**: Also, ich kenne `rw [{h}]` und `apply ({h}.mp)`, aber das wollten wir ja
    diesmal vermeiden.

    **Robo**: Was du machen könntest, ist, mit `obtain ⟨mp, mpr⟩ := {h}` die Annahme
    in zwei Teile aufteilen."
  Branch
    intro
    Hint "
      **Robo**: Hier müsstest du jetzt `rw [←{h}]` oder `apply {h}.mp` benutzen.
      Geh lieber einen Schritt zurück, sodass das Goal `A → B` ist."
  obtain ⟨mp, _mpr⟩ := h
  Hint (hidden := true) "**Du**: Ah, und jetzt ist das Beweisziel in den Annahmen."
  assumption

Conclusion
"
**Operationsleiter**: Perfekt, das sollte reichen!
"

OnlyTactic intro obtain assumption
DisabledTactic rw apply tauto
