-- Level name : Impliziertes Chaos

/-
Da Aussagen einfach Typen sind, ist eine Implikation einfach eine Funktion `(h : A → B)`,
die  einen Beweis von `A` nimmt und damit einen Beweis von `B` erzeugt.. Wenn man einen
Beweis `(ha : A)` hat, dann ist `h ha` ein Beweis von `B`.
-/

/- Hint : apply
Du hast zwei Möglichkeiten, hier Fortschritt zu machen.
Erstens, Wenn das Goal Typ `G` hat, und du eine Annahme vom Typ `h : X → G` hast (also in unserem Fall
wär das ein Lemma "X impliziert G"), kannst du mit `apply h` diese verwenden. Jetzt musst du nur noch
`X` beweisen.

Du arbeitest dich also Rückwärts durch den Beweis. Das Äquivalent auf Papier ist so etwas wie
"Es genügt zu zeigen, dass".
-/

/- Hint : Und die Zweite?
Die zweite Möglichkeit, ist dass du dir neue Zwischenergebnise erstellst:
Wenn `ha : A` ein Beweis von `A` ist und `f : A → B`, dann ist mit
`have hb := f ha` danach ein Beweis von `B`.

Dies ist die ungünstigere Option, da man ganz viele Zwischenergebnise rumschwirren hat,
aber prinzipiell kannst du frei auswählen.
-/

variables {A B C D E F G H : Prop}

/- Lemma : no-side-bar
Sei `ha` ein Beweis der Aussage `A`. Zeige Anhand der verschiedenen Implikationen
dass Aussage `G` wahr ist.
-/
lemma impliziertes_chaos (ha : A) (f : C → H)
  (g : F → C) (h : B → E) (i : H → F) (j : A → F)
  (k : B → G) (m : A → D) (n : H → G) (p : D → F) : G :=
begin
  apply n,
  apply f,
  apply g,
  apply j,
  exact ha,
end

/- Tactic : apply
`apply h` wendet eine Annahme `h : A → B` auf ein Goal vom Typ `B`.
-/

/- Tactic : have
`have h : A := _` speichert ein Zwischenresultat vom Typ `A` unter dem Namen `h` ab.
Für den Platzhalter `_` kommt dann der Beweis, also ein Element vom richtigen Typ, oder
ein `begin ... end`-Block, der ein solches mit Taktiken konstruiert.
-/
