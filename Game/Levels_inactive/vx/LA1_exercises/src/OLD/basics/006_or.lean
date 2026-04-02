-- Level name : 

/-
Wir haben schon gesehen, dass `(A : Prop)` eine algemeine logische Annahme definiert, ohne
anzugeben, ob diese wahr oder falsch ist, und dass dann `(hA : A)` ein Beweis wäre, dass
Aussage `A` wahr ist.

Logische Aussagen kann man dann miteinander verknüpfen, wir schauen uns nun die folgenden
logischen Operationen an:

- `¬`, Nicht (`\not`)
- `∨`, Oder (`\or`)
- `∧`, Und (`\and`)
- `→`, Implikation (`\to`)
- `↔`, Genau-dann-wenn (`\iff`)
- `∀`, Für alle (`\forall`)
- `∃`, Existiert (`\exists`)
- `∃!`, Existiert genau ein (`\exists` + `!`)

Zuerst das "Oder", `∨`.

Bei einem `∨` im Goal kann man mit `left` oder `right` entscheiden, welche Seite man denn zeigen
möchte.

-/

variables (A B : Prop)

/- Lemma : no-side-bar
Angenommen `A` ist wahr, zeige dass "A oder (nicht B)" (`A ∨ (¬ B)`) wahr ist.
-/
lemma klar_oder_nicht (hA : A) : A ∨ (¬ B) :=
begin
  left,
  exact hA,
end

/- Tactic : left/right
Entscheidet bei ODER `∨` ob man die linke oder rechte Seite beweisen möchte.
-/
