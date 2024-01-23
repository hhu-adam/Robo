-- Level name : Natürliche Zahlen

/-
In diesem Level lernst du die natürlichen Zahlen `ℕ` kennen und wie man mit ihnen rechnet.

Zuerst ist es wichtig, zu verstehen wie die natürlichen Zahlen definiert sind.

```
inductive ℕ
| zero : ℕ
| succ (n : ℕ) : ℕ
```

`ℕ` besteht aus zwei Teilen: einer Null `0` und einer Nachfolgerfunktion `succ : ℕ → ℕ`.
`1` ist dann z.B. `0.succ` und `2` ist `0.succ.succ`.

Eine Funktion wie `(a + _) : ℕ → ℕ` wird dann auch immer in zwei Teilen definiert:

- Was ist `a + 0`?
- Was ist `a + b.succ`?

Deshalb kann `refl` das folgende Beispiel beweisen, denn per Definition ist `a + 0 = a`.
-/

/- Axiom : add_zero
`a + 0 = a`.
-/

lemma add_zero (a : ℕ) : a + 0 = a :=
begin
  refl
end

/-
Allerdings umgekehrt kann `refl` das Lemma `0 + a = a` nicht lösen, denn da findet intern
noch die Fallunterscheidung `0 + 0 = 0` und `0 + b.succ = b.succ` statt.

Hier braucht man am besten **Induktion**: `induction a with n hn` teilt das Goal `0 + a = a`
in die einzelnen Fälle auf.

(Bemerkung: Anstatt `induction a` kannst du auch abundzu `cases a` verwenden, welches du schon kennst.
Der Unterschied ist lediglich, dass man bei `cases` im Fall `a.succ` dann keine Induktionsannahme
zur Verfügung hat.)
-/

/- Hint: nat.add_succ
Die vier Lemmas `nat.add_succ`, `nat.succ_add`, `nat.mul_succ`, `nat.succ_mul` helfen
dir weiter. Z.B. schreibt `nat.add_succ` `a + b.succ` zu `(a + b).succ` worauf
du innerhalb der Klammern die Induktionshypothese anwenden kannst.
-/

/- Lemma :
Beweise durch Induktion.
-/
lemma zero_add (a : ℕ) : 0 + a = a :=
begin
  -- exact nat.zero_add a,
  induction a with a ha,
  refl,
  rw nat.add_succ,
  rw ha,
end

/- Axiom : nat.succ_add
`a.succ + b = (a + b).succ`.
-/

/- Axiom : nat.add_succ
`a + b.succ = (a + b).succ`.
-/

/- Axiom : nat.mul_succ
`a.succ * b = a * b + b`.
-/

/- Axiom : nat.succ_mul
`a * b.succ = a * b + a`.
-/

