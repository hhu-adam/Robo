import Game.Metadata
import Game.Levels.Cantor.L07_idempotent

World "Cantor"
Level 8

Title ""

Introduction
"
Cantor landet, steigt vom Rad, kommt wieder zur Bühnenkante und reibt sich die Hände.

**Cantor**: Ihr kommt der Sache jetzt näher!
Wenn ihr genau hinseht, habt ihr eine Abbildung vor euch,
die auf einem Produkt `A × A` definiert ist!
Und im Produkt gibt es eine Diagonale!
"

Conclusion
"
  **Cantor**:  Sehr schön!

  Er klatscht.

  **Du**:  Also ich verstehe gerade gar nichts mehr.
"

open Function Set

Statement {A Y : Type} {f : A → A → Y} {s : Y → Y}
     {a : A} (ha : f a = fun a' ↦ s (f a' a')) :
    IsFixedPt s (f a a) := by
  Hint "
    **Du** *(zu Robo)*: Siehst du hier ein Produkt?

    **Robo**:  Ja, klar.  Erinner dich, wo bei `f` die Klammern stehen: `A → (A → Y)`.
    Eine Abbildung von `A` zur Menge der Abbildungen von `A →  Y` ist doch dasselbe
    wie eine Abbildung von `A × A` nach `Y`.

    Du runzelst die Stirn.

    **Robo**: Doch doch, das hatte wir uns auf Epo schon einmal überlegt!
    Du kannst `{f} {a} {a}` entweder als `{f} {a}` angewendet auf `{a}` oder als
    `{f}` angewendet auf `({a},{a})` interpretieren.

    **Cantor**:  Ganz genau!  Und das Element `({a},{a})` liegt auf der Diagonale!

    **Robo**: Die Annahme `{ha}` ist andereseits so formuliert,
    dass die Interpretation von `f` als Abbildung `A → (A → Y)` naheliegender ist.
    "
  unfold IsFixedPt
  apply congr_fun at ha
  specialize ha a
  rw [← ha]


TheoremTab "Function"
