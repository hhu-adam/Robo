import Game.Metadata

World "Proposition"
Level 10

Title "Und"

Introduction
"
Der nächste Formalosoph in der Reihe hat seine Frage bereìts mitgebracht.
Er legt sie uns vor, setzt sich hin und häkelt.
"
/--  -/
Statement (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  Hint "
    **Du**:  Also, wir haben zwei Annahmen: `{A}` gilt, und `{B}` gilt auch. Und beweisen sollen wir
    dass `{A} und {B}` gilt. Ich glaube, diese Formalospinner treiben mich noch zur Verzweiflung.
    Kann ich nicht wieder `trivial` sagen?

    **Robo**: Nee, diesmal wird das nicht funktionieren.
    Du musst das Beweisziel einfach in zwei Teile zerlegen. Probier mal `constructor`.

    **Du**: Du meinst, `destructor`??

    **Robo**: Nein, `constructor`. Ich weiß das ist verwirrend,
    aber die nennen das hier so weil man die Aussage aus mehreren Teilen
    konstruieren kann."
  constructor
  -- gleicher Hint wie unten!
  assumption
  Hint (hidden := true) "
    **Robo**: Schau mal, das ist Zauberpapier.
    Jetzt haben wir auf einmal zwei Beweisziele.
    Hier ist dast Ziel `{B}`.
    Ich glaube, du weißt schon, wie man die jeweils erreicht.
    Die Ziele stehen ja jeweils in den *Annahmen*."
  assumption

Conclusion
"
**Robo**: Super!

Ihm scheinen diese Fragen inzwischen Spaß zu machen.

**Robo**: Meinst du, dieser Hebel, an dem \"Editor mode\" steht, ist echt?
Oder ist der nur gemalt?  Probier mal!
"

/--
`constructor` teilt ein Goal auf, wenn das Goal eine Struktur ist

## Detail
Wenn das Goal eine Struktur ist, wie z.B. `A ∧ B` welches zwei Felder hat `⟨A, B⟩`, dann
erzeugt `constructor` ein Goal pro Feld der Struktur.

## Hilfreiche Resultate

* Das Gegenteil von `constructor` ist `⟨_, _⟩` (`\\<>`), der *anonyme Konstruktor*.
Dieser enspricht ungefähr der Tupel-Notation in
\"eine Gruppe ist ein Tupel $(G, 0, +)$, sodass …\".

## Beispiel

```
example {A B : Prop} (h : A) (g : B) : A ∧ B := by
  constructor
  · assumption
  · assumption
```
-/
TacticDoc constructor

NewTactic constructor
DisabledTactic tauto
