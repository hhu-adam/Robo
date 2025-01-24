-- Level name : Logisch, oder?

/-
Ohne in die Details von "dependent Type Theory" zu gehen, sind in Lean alles Typen und
man kann Elemente von diesen Typen haben, welche wiederum selber Typen sind.

Hier definieren wir zwei Typen `U` und `V`:
-/

variables {U V : Type*}

/-
Später können wir dann diesen Typen Eigenschaften geben wie zum Beispiel `[ring U]`, was sagt,
dass der Typ `U` eine Ringstruktur haben soll, aber das kommt später.

Für jetzt können wir Elemente aus diesen Typen mit `(x y : U)` auswählen und wir können
Abbildungen zwischen zwei Typen definieren: `(f : U → V)` (`\to`). Wir sagen hier nicht was `f` ist,
sondern nur, dass es eine beliebige solche Funktion ist, also ein Element vom Typ `U → V`.

Ein wichtiger Typ ist `Prop`, der Typ aller mathematischen Aussagen (wahre, falsche, nicht entscheidbare).
Aussagen sind Elemente von diesem Typ `(A B : Prop)` und ein Beweis der Aussage `A`
ist einfach ein Element vom Typ `A`, also `(ha : A)`.

Seien `A` und `B` also Aussagen:
-/

variables (A B : Prop)

/-
Die wichtigsten Notationen für Logik sind die folgenden:

- `∧`, und (`\and`)
- `∨`, oder (`\or`)
- `¬`, not (`\not`)
- `→`, impliziert (`\to`)
- `↔`, genau-dann-wenn (`\iff`)
- `∀`, für alle (`\forall`)
- `∃`, existiert (`\exists`)

Im folgenden lernen wir anhand dieser die wichtigsten Taktiken kennen.
Zuerst, wenn man ein OR im Goal hat.
-/

/- Hint : Triff eine Auswahl.
Bei einem OR kann man mit `left` oder `right` entscheiden, welche Seite man denn zeigen
möchte.
-/

/- Tactic : left/right
Entscheidet bei ODER `∨` ob man die linke oder rechte Seite beweisen möchte.
-/

/- Lemma : no-side-bar
Angenommen `A` ist wahr, zeige dass "A oder (nicht B)" (`A ∨ (¬ B)`) wahr ist.
-/
lemma klar_oder_nicht (ha : A) : A ∨ (¬ B) :=
begin
  left,
  exact ha,
end
