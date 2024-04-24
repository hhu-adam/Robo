-- Level name : Eins und Null

-- begin hide
import basics.numbers.nat_001b
-- end hide

/-
Nun wollen wir ein paar mehr wichtige Lemmas kennen lernen, um mit `ℕ` zu rechnen.
Diese kannst du jeweils mit `rw [one_mul]` anwenden. Die Lemmanamen setzen sich aus den Operationen
zusammen, so heisst das Lemma `1 * a = a` entsprechend `one_mul`.

`rw [one_mul]` wendet das Lemma einfach einmal an, und zwar am ersten Ort, wo es kann.
-/

/- Lemma : no-side-bar
Finde die Lemmas `add_zero`, `zero_add`, `mul_zero`, `zero_mul`, `mul_one`, `one_mul`
links bei den bekannten Lemmas und benutze diese, um folgendes zu beweisen.
-/
example (a b c : ℕ)  : 0 * 0 * b + (a + 0) * 1 + 1 * c = a + c :=
begin
  rw [zero_mul, zero_mul, zero_add, add_zero, mul_one, one_mul],
end


/- Axiom : mul_one
`a * 1 = 1`.
-/

/- Axiom : one_mul
`1 * a = a`.
-/

/- Axiom : mul_zero
`a * 0 = 0`.
-/

/- Axiom : zero_mul
`0 * a = 0`.
-/
