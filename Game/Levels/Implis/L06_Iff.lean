import Game.Metadata

World "Implis"
Level 6

Title "" -- "Genau dann, wenn"

/-
Introduction
"
**Operationsleiter**: Wir hatten auch mal ein paar Förderbänder, die in beide Richtungen laufen
konnten. Die hatte ich vorsichtshalber alle abgestellt, weil in den neusten Handbüchern von
solchen Doppelbändern abgeraten wird. Aber vielleicht sind sie ja unter bestimmten
Voraussetzungen doch sicher? Was meint Ihr zu diesem Fall?
"
-/
Introduction "`INTRO` Intro Implis L06"

Statement (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  /-
  Hint "
    **Robo**: `A ↔ B` ist natürlich Leansch für $A \\iff B$, also genau-dann-wenn.
    Die Aussage `A ↔ B` besteht also aus zwei Teilen; sie ist als `⟨A → B, B → A⟩` definiert.

    **Du**: Also ganz ähnlich wie das UND, `A ∧ B`?

    **Robo**: Genau. Entsprechend kannst du auch hier mit `constructor` anfangen."
  -/
  Hint "`A ↔ B` is Leanic for $A \\iff B$. `A ↔ B` consists of two parts. It is defined as `⟨A → B, B → A⟩`.
  It is a similar defintion to `A ∧ B`. Start with `constructor`"
  constructor
  -- Hint "**Du**: Ah, und die beiden Teile habe ich schon in den Annahmen."
  Hint "`COMMENT` parts available in assumptions"
  assumption
  assumption

/-
Conclusion
"
**Operationsleiter**: Okay, das leuchtet mir ein.

**Robo** *(zu dir)*: Übrigens, so wie bei `(h : A ∧ B)` die beiden
Teile `h.left` und `h.right` heißen,
heißen bei `(h : A ↔ B)` die beiden Teile `h.mp` und `h.mpr`.

**Du**: Also `h.mp` ist `A → B`? Wieso `mp`?

**Robo**: `mp` steht für Modus Ponens. Der Modus ponens ist eine schon in der antiken
Logik geläufige Schlussfigur, die in vielen logischen Systemen … Ach nee, das wolltest
du ja nicht hören. Das \"r\" in `mpr` steht für \"reverse\", weil's die Rückrichtung ist.
"
-/
Conclusion
"
Conclusion Implis L06: Explain that analogous to `(h : A ∧ B)` with `h.left` and `h.right`,
`(h : A ↔ B)` has `h.mp` and `h.mpr`. `h.mp` can be understood as `A → B`. It is `mp` as `mp`
stands for Modens Ponens. The 'r' in `mpr` stands for 'reverse'.
"

NewDefinition Iff
DisabledTactic tauto rw
