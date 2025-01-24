-- Level name : Übung macht den Meister

variables (A B : Prop)

/-
Du kennst fast alles, um folgende Aufgabe zu lösen, aber...

Eine Richtung der Aussage `(A ∨ B) ↔ (¬ A → B)` kann man
nur zeigen, indem man die beiden Fälle betrachtet: entweder ist `A` wahr oder falsch
(auch "law of excluded middle" genannt).

`by_cases h : A` teilt das Goal in zwei Teile, wobei es zuerst animmt, dass `A` wahr ist
`(h : A)` und danach dass `A` falsch ist `(h : ¬ A)`.

Wichtig: `cases` / `by_cases` sowie `contradiction` / `by_contradiction` sind
jeweils komplett veschiedene Taktiken!
-/

/- Hint : ?
Eine Annahme (h : A ∨ B) kannst du mit `cases h` in zwei Fälle aufteilen.
-/

/- Lemma :
Zeige folgende äquivalente Form von ODER:
-/
lemma or_iff_not_imp_left : (A ∨ B) ↔ (¬ A → B) :=
begin
  constructor,
  { intros h a,
    cases h,
    { contradiction },
    { exact h }},
  { intro h,
    by_cases ha : A,
    { left,
      exact ha },
    { right,
      apply h,
      exact ha }},
end

/- Tactic : by_cases
`by_cases h : A` betrachtet die beiden Fälle `A` und `¬ A` separat.

Bsp: Für eine Zahl `p` kann man auch dann
`by_cases hp : p = 0` machen um `p = 0` und `p ≠ 0` zu unterscheiden.
-/