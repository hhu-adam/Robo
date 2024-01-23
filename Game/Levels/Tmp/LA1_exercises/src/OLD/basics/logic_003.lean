-- Level name : Logik zum aufteilen.

/-
"Und" wir mit `∧` `\and` geschrieben und genau-dann-wenn
wird mit `↔` ("if-and-only-if", `\iff`) geschrieben.

Die beiden haben die Gemeinsamkeit, dass sie beide aus zwei Einzelteilen definiert sind:
- `A ∧ B` besteht aus der linken und rechten Seite,
- `A ↔ B` besteht aus der Richtungen `A → B` und `B → A`.
-/

/- Hint : Anfang
Bei genau-dann-wenn (if-and-only-if, `↔`, `\iff`) und dem logischen UND (`∧`, `\and`) muss man
zwei Sachen zeigen, beide Richtungen oder beide Seiten. In Lean teilst du ein solches Goal
mit `constructor` in die einzelnen Goals auf.
-/

/- Hint : Man wähle ein X.
Wenn das Goal von der Form `X → Y` ist, kann man mit `intro h` annehmen, dass man einen Beweis
für `X` hat, der `h` heisst.

`intros h h' hh` könnte mehrere `intro` zusammenfassen.
-/

/- Hint : Aufteilen.
Um die Annahme `h : A ∧ B` aufzuteilen, hast du zwei Möglichkeiten:
- `cases h with ha hb` trennt `h` in die einzelnen Aussagen `(ha : A)`, `(hb : B)`.
- Mit `h.1` und `h.2` kannst du auf diese direkt zugreifen.
-/

/- Lemma : no-side-bar
  Beweise folgende Aussage:
-/
lemma zum_teilen (A B : Prop) : (A ∧ (A → B)) ↔ (A ∧ B) :=
begin
  constructor,
  { intro h,
    cases h with h₁ h₂,
    constructor,
    { exact h₁ },
    { exact h₂ h₁ }},
  { intro h,
    cases h with h h',
    constructor,
    exact h,
    intro,
    exact h' },
end

/- Tactic : intro/intros
Wenn das Goal von der Form `A → B` ist, dann nimmt man mit `intros h` an,
dass `A` wahr ist. (Konkret erhält man dann einen Beweis von `A` mit dem Namen
`h`, also ein Element von `A`, geschrieben `(h : A)`.)
-/

/- Tactic : constructor
Versucht ein Goal in Teilgoals aufzuteilen.
Bsp: `A ↔ B` wird aufgeteilt in `A → B` und `B → A`.
Bsp: `A ∧ B` wird aufgeteilt in `A` und `B`.
-/

/- Tactic : cases
Für Annahmen von der Form `h : A ∧ B` kann man mit
`cases h with h₁ h₂` diese aufteilen.

Alternativ könnte man beide Seiten direkt mit `h.1`
und `h.2` verwenden.
-/
