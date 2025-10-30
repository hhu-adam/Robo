import Game.Metadata
import Game.Levels.Cantor.L07_idempotent

World "Cantor"
Level 8

Title ""

/-
Introduction
"
Cantor landet, steigt vom Rad, kommt wieder zur Bühnenkante und reibt sich die Hände.

**Cantor**: Ihr kommt der Sache jetzt näher!
Wenn ihr genau hinseht, habt ihr eine Abbildung vor euch,
die auf einem Produkt `A × A` definiert ist!
Und im Produkt gibt es eine Diagonale!
"
-/
Introduction "Intro Cantor L08: Mapping defined on product `A × A` with diagonal"

/-
Conclusion
"
  **Cantor**:  Sehr schön!

  Er klatscht.

  **Du**:  Also ich verstehe gerade gar nichts mehr.
"
-/
Conclusion "`CONC`Conclusion Cantor L08"

open Function Set

Statement {A Y : Type} {f : A → A → Y} {s : Y → Y}
     {a : A} (ha : f a = fun a' ↦ s (f a' a')) :
    IsFixedPt s (f a a) := by
  /-
  Hint "
    **Du** *(zu Robo)*: Siehst du hier ein Produkt?

    **Robo**:  Ja, klar.  Erinner dich, wo bei `f` die Klammern stehen: `A → (A → Y)`.
    Eine Abbildung von `A` zur Menge der Abbildungen von `A →  Y` ist doch dasselbe
    wie eine Abbildung von `A × A` nach `Y`.

    Du runzelst die Stirn.

    **Robo**: Doch doch, das hatten wir uns auf Epo schon einmal überlegt!
    Du kannst `{f} {a} {a}` entweder als `{f} {a}` angewendet auf `{a}` oder als
    `{f}` angewendet auf `({a},{a})` interpretieren.

    **Cantor**:  Ganz genau!  Und das Element `({a},{a})` liegt auf der Diagonale!

    **Robo**: Die Annahme `{ha}` ist andereseits so formuliert,
    dass die Interpretation von `f` als Abbildung `A → (A → Y)` naheliegender ist.
    "
  -/
  Hint "Explain for `f`, that `A → (A → Y)` is a mapping from `A` to the set of mappings of `A →  Y`,
  which in turn is the same as the mapping from `A × A` to `Y`. You can interpret `{f} {a} {a}` either
  as applying `{f} {a}` onto `{a}` or applying `{f}` onto `({a},{a})`. The element `({a},{a})` lays
  on the diagonal. Assumption `{ha}` is formulated s.t. the interpretation of `f` as `A → (A → Y)`
  natural"
  unfold IsFixedPt
  Branch
    rw [ha]
    /-
    Hint "**Robo**:
      Jetzt hast du im wesentlichen beide Vorkommen von `f a a` durch `s f a a` ersetzt.
      Damit drehst du dich im Kreis.  Wahrscheinlich willst du nur das zweite Vorkommen
      von `f a a` im Beweisziel umschreiben.  Das machst du mit `nth_rw 2 [{ha}]`.
    "
    -/
    Hint "`f a a` was replaced by `s f a a`. It is probably necessary to rewrite the second
    appearnace of `f a a` in the goal. Try `nth_rw 2 [{ha}]`"
    simp
  Branch
    nth_rw 2 [ha]
  apply congr_fun at ha
  specialize ha a
  rw [← ha]


TheoremTab "Function"
