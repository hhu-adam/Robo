import Game.Metadata


World "Logo"
Level 14

Title "" -- "Zusammenfassung"

Introduction
"
Der letzte Untertan tritt vor. Ihr Anliegen ist etwas komplizierter als die vorherigen.

**Robo** Wirf einfach alles drauf, was du gelernt hast.
Hier, ich bin sogar so nett und zeig dir noch einmal die vier
wichtigsten Taktiken für diese Situation an.

| (Übersicht) | Und (`∧`)                | Oder (`∨`)              |
|:------------|:-------------------------|:------------------------|
| Annahme     | `obtain ⟨h₁, h₂⟩ := h`   | `obtain h \\| h := h`   |
| Goal        | `constructor`            | `left`/`right`          |
"

-- Note: The other direction would need arguing by cases.

Statement (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  Hint (hidden := true)
    "**Robo**: Ich würd zuerst die Annahme {h} mit `obtain ⟨⟩ := {h}` aufteilen."
  Branch
    constructor
    · obtain h' | h' := h
      · left
        assumption
      · obtain ⟨h₁, _h₂⟩ := h'
        right
        assumption
    · obtain h' | h' := h
      · left
        assumption
      · obtain ⟨_h₁, h₂⟩ := h'
        right
        assumption
  obtain h | h := h
  Hint (hidden := true) "**Robo**: Jetzt kannst du das `∧` im Goal mit `constructor` angehen."
  · constructor
    · left
      assumption
    · left
      assumption
  · Hint (hidden := true)
      "**Robo**: Hier würde ich die Annahme {h} nochmals mit `obtain` aufteilen."
    Branch
      constructor
      · Hint "**Robo**: Der Nachteil an der Reihenfolge ist, dass du jetzt in jedem Untergoal
          `obtain ⟨⟩ := h` aufrufen musst."
        Branch
          right
          obtain ⟨h₁, _h₂⟩ := h
          assumption
        obtain ⟨h₁, _h₂⟩ := h
        right
        assumption
      · Branch
          right
          obtain ⟨_h₁, h₂⟩ := h
          assumption
        obtain ⟨_h₁, h₂⟩ := h
        right
        assumption
    obtain ⟨h₁, h₂⟩ := h
    constructor
    · right
      assumption
    · right
      assumption

Conclusion
"
**Robo** Bravo! Jetzt aber nichts wie weg hier, bevor sich eine neue Schlange bildet!

Königin *Logisinde* ist in der Zwischenzeit eingeschlafen, und ihr stehlt euch heimlich davon.
"

DisabledTactic tauto
