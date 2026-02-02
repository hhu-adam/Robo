import Game.Metadata

World "Quantus"
Level 8

Title "" -- "PushNeg"

/-
Introduction
"
**Robo**: Während wir warten, zeig ich dir vielleicht kurz, wie sich Negation mit Quantoren verträgt. Ich habe so ein Gefühl, dass wir das gleich brauchen werden.
"
-/
Introduction "Intro Quanus L08"


open Function

Statement {X : Type} (P : X → Prop) :
    ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  /-
  Hint "
    **Du**: Was ist denn jetzt dieses `{P}`?

    **Robo**: `{P}` ist ein „Prädikat“; eine Aussage über Objekte vom Typ `{X}`.
              Zum Beispiel könnte `{X}` wieder der Typ der natürlichen Zahlen sein.
              Und `{P} x` könnte die Aussage sein:
              Die natürliche Zahl `x` ist gerade. Oder: `x` hat sieben Primfaktoren. Oder: `x`
              ist Robo's Lieblingszahl. Oder …

    **Du**: Schon gut, ich glaub ich habs verstanden. `{P}` ist sozusagen eine Abbildung, die
    ein Element `x : {X}` nimmt und auf eine Aussage wirft.

    **Robo**: Ja, sozusagen.

    **Du**: Gut. Dann ist auch ziemlich klar, was hier die Aussage ist.
            Und du wolltest mir jetzt verraten, wie ich das auf Leansch zeige?

    **Robo**: Genau. Was du brauchst, ist `push_neg`."
  -/
  Hint "Explain `{P}`: `{P}` is an expression over the type `{X}`. `{X}` could e.g. be the natural
  numbers. `{P} x` could be the expression: `x` is even. Or: `x` has seven prime factors. Or: `x` is
  a favorite number. In other words: `{P}` is a mapping that takes `x : {X}` and maps it onto an expression.
  Try `push_neg`."
  Branch
    constructor
    intro h
    -- Hint (hidden := true) "
    --  **Robo**: `push_neg` schiebt von links nach rechts. Du kannst es hier also nicht auf
    --  das Beweisziel anwenden, wohl aber auf `{h}`."
    Hint (hidden := true) "Try `push_neg` at `{h}`"
    push_neg at h
    assumption
    intro h
    push_neg
    assumption
  push_neg
  rfl

NewTactic push_neg
DisabledTactic tauto

/-
Conclusion
"
**Robo**: Gut gemacht. Intern benutzt `push_neg` übrigens zwei Lemmas:

 - `not_exists (P : X → Prop) : ¬ (∃ x, P x) ↔ ∀ x, (¬ P x)`
 - `not_forall (P : X → Prop) : ¬ (∀ x, P x) ↔ ∃ x, (¬ P x)`

Das erste Lemma ist die Aussage, die du gerade gezeigt hast.

**Du**: Na toll. Ich habe die Aussage also gezeigt, indem ich sie benutzt habe …

**Robo**: :-) Hauptsache, Du merkst dir `push_neg`.
"
-/
Conclusion "Conclusion Quantus L08: `push_neg` internally uses `not_exists (P : X → Prop) : ¬ (∃ x, P x) ↔ ∀ x, (¬ P x)`
and `not_forall (P : X → Prop) : ¬ (∀ x, P x) ↔ ∃ x, (¬ P x)`. Memorize `push_neg`.
"
