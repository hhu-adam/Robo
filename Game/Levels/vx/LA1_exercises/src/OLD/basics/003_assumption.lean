-- Level name : Annahmen

/-
Um Aussagen zu formulieren braucht man Annahmen. Zum einen sind das Objekte, von denen eine Aussage handelt,
wie zum Beispiel "sei `n` eine natürliche Zahl", oder "seien `A`, `B` logische Aussagen", zum anderen
sind dass Annahmen wie "angenommen dass `n` nicht Null ist" oder "angenommen `A` ist wahr".

In Lean schreibt man beides mit der gleichen Notation: `(n : ℕ)` ist eine natürliche Zahl, 
`(A B : Prop)` sind Aussagen, `(h : n ≠ 0)` ist eine Annahme, dass `n` nicht Null ist, und
`(hA : A)` ist die Annahme, dass `A` wahr ist (`hA` ist ein Beweis von `A`).

Die Annahmen kommen dann vor den Doppelpunkt oder vor dem Lemma also `variables (n : ℕ)`.
Beide Schreibweisen sind äquivalent, der Unterschied ist nur, dass eine Annahme in einer
`variables`-Zeile dann für alle folgenden Lemmas zur Verfügung steht.

```
/-- Sei n eine natürliche Zahl ungleich Null. Dann ist n strickt grösser als Null. -/
example (n : ℕ) (hn: n ≠ 0) : 0 < n :=
begin
  sorry
end

/-- Seien A und B logische Aussagen und A sei wahr. Dann ist "A oder B" wahr. -/
example (A B : Prop) (hA: A) : A ∨ B :=
begin
  sorry
end
```

Wenn eine Annahme `h` genau dem Goal entspricht, kannst du `exact h` verwenden.
-/

variables (n : ℕ)

/- Lemma : no-side-bar
Wenn `n = 0` dann ist `n = 0`.
-/
example (h : n = 0) : n = 0 :=
begin
  exact h,
end

/-
Alternativ kannst du `assumption` brauchen, welches automatisch nach der richtigen
Annahme sucht.
-/

/- Lemma : no-side-bar
Wenn `n = 0` dann ist `n = 0`.
-/
example (h : n ≠ 0) : n ≠ 0 :=
begin
  assumption,
end

/- Tactic : exact
`exact h` schliesst den Beweis wenn `h` und das Goal exact übereinstimmen.
`assumption` funktioniert gleich, sucht aber selbständig, welche Annahme mit dem Goal
übereinstimmt.
-/

/- Tactic : assumption
`assumption` sucht in den Annahmen nach einer, die mit dem Goal übereinstimmt, und schliesst den Beweis.
-/

/- Typen : `Prop`, `ℕ` -/