-- Level name : Implikation

/-
Logische Aussagen können einander implizieren. Wir kennen hauptsächlich zwei Zeichen dafür:
`A ↔ B` (`\iff`) bedeutet "Genau dann wenn" und `A → B` (`\to`) bedeutet "`A` impliziert `B`".

Wenn man Aussage `B` beweisen will und eine Implikationsannahme `(h : A → B)` hat, dann kann man
diese mit `apply h` anwenden.
Auf Papier würde man schreiben, "es genügt zu zeigen, dass `A` stimmt, denn `A` impliziert `B`".
-/

variables (A B : Prop)

/- Lemma : no-side-bar
Falls `A` wahr ist und "`A` impliziert `B`", dann ist `B` wahr.
-/
example (hA : A) (g : A → B) : B :=
begin
  apply g,
  exact hA,
end

/-
Alternative kann man mit `specialize g hA` auch vorwärts argumentieren.
`specialise g hA` nimmt eine Implikation `(g : A → B)` und einen Beweis `(hA : A)`
und überschreibt dann `g` mit einem Beweis von `B`, also `(g : B)`.
-/

/- Lemma : no-side-bar
Falls `A` wahr ist und "`A` impliziert `B`", dann ist `B` wahr.
-/
example (hA : A) (g : A → B) : B :=
begin
  specialize g hA,
  assumption,
end

/- Tactic : apply
"es genügt zu zeigen, dass"

`apply h` wendet eine Annahme `(h : A → B)` auf ein Goal vom Typ `B` an.
-/

/- Tactic : specialize
`specialize h a` nimmt eine Implikation `(h : A → B)` und einen Beweis `A`, `(a : A)`,
und produziert einen Beweis von `B`, `(b : B)`.
-/

