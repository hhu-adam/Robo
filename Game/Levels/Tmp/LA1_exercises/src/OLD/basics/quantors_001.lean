-- Level name : Quantoren

import tactic.interactive

/-
Weitere grundlegende Logik-Elemente sind die Quantoren `∀` und `∃`.

Der volle Syntax sieht wie folgt aus: `∀ (x : U), f x = 0` oder `∃ (x : U), f x = 0`.
Der Typ von `x` wird oft weggelassen, wenn Lean ihn ermitteln kann.
Das Komma `,` trennt die Variablen vom Statement.

- Ein `∀` im Goal kann immer mit `intro` beseitigt werden.
- Eine Annahme `(h : ∀ x, P x)` kann man auf ein Element `y` anwenden
  um `P y` zu erhalten: `have hy : P y := h y`.
- Ein `(h : ∃ x, ...)` in den Annahmen kann man mit `cases h with x hx` beseitigen und tatsächlich
  ein solches `x` auswählen.
- Ein `∃` im Goal muss man konkret erstellen. Wenn man also ein `x` hat, kann man
  `use x` benutzen, um dieses einzuführen.
- Um ein neues Zwischenresultat mit `∃` zu erstellen, braucht man die
  Konstruktor-Schreibweise `⟨ , ⟩`:
  `have h_new : ∃ x, P x := ⟨y, Py⟩` (angenommen man hat `y` und den Beweis `P y` schon).
-/

variables {U : Type*} (P : U → Prop)

variable [decidable (∃ x, P x)]

/- Hint : Anfang
Wie du bei einem `↔` anfängst, solltest du schon kennen.
-/

/- Hint : ?
`¬∃ (x : U), P x`
Auch schon bekannt, ein `¬` gehst du am besten mit `by_contradiction h` an.
-/

/- Hint : ?
Ein `(h : ∃ x, ...)` in den Annahmen kannst du mit `cases h with x hx` aufsplitten
und tatsächlich ein solches `x` auswählen.
-/

/- Hint : Gegenrichtung, after `by_contradiction`.
Von hier hast zwei Möglichkeiten:
1) Da eine Annahme `(h : ¬∃ (x : U), P x)` im Grunde `(h : ∃ (x : U), P x → false)` ist,
   kannst du mit `apply h` Fortschritt machen und danach `use` benutzen.
2) oder kreeire einen direkten Widerspruch zu `(h : ¬∃ (x : U), P x)` mit
   `have h' : ∃ x, P x := ⟨_, _⟩` (und ersetzt die `_`).
-/

/- Lemma : no-side-bar
Beweise.
-/
lemma nicht_fuer_alle : (∀ x, ¬ P x) ↔ ¬ ∃ x, P x :=
begin
  constructor,
  {
    intro h,
    by_contradiction h2,
    cases h2 with x hx,
    have h' := h x,
    contradiction
  },
  {
    intros h x,
    by_contradiction h2,

    apply h, -- did not introduce `apply` yet.
    use x,
    exact h2,

    -- have hh : ∃ x, P x := ⟨x, h2⟩, -- alternative proof
    -- contradiction
  }
end
