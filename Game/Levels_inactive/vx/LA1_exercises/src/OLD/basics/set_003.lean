-- Level name : Elemente

-- begin hide
import basics.set_theory.set_001
import data.set.finite
import set_theory.cardinal.basic
import data.set.countable
-- end hide

/-
Häufig will man Mengen anhand von bestimmten Konditionen erstellen. z.B Die Teilmenge aller geraden Zahlen
in `ℤ`. Lean braucht dafür den folgenden Syntax: `{n : ℤ | ∃ k, n = 2 * k}`.

Wichtig ist hier die Ähnlichkeit zur Subtyp-Notation, der du schon kurz bei `ℕ+` begegnet bist:

`{n : ℤ | ∃ k, n = 2 * k}` ist eine Menge, hat also Typ `set ℤ`. 
`{n : ℤ // ∃ k, n = 2 * k}` ist hingegen selber wieder ein Typ (das heisst "Subtype notation").
Wenn du mit Mengen arbeitest, willst du eigentlich immer die erste Variante.

Wenn man bereits ne Menge hat, wie zum Beispiel eien Teilmenge von `ℤ`, `(A : set ℤ)`, dann kann man mit
`{x ∈ A | ∃ (k : ℤ), n = 2 * k}` die Teilmenge.

(Auch hier wäre `{n : C | ∃ (k : ℤ), n = 2 * k}` falsch, der Ausdruck oben ist eher äquivalent zu
`{n : ℤ | n ∈ A ∧ ∃ (k : ℤ), n = 2 * k}`.)

-/

open set

variables {X : Type*} (x : X) (A B : set X)

#check set.eq_of_mem_singleton
#check {n : ℤ | ∃ k, n = 2 * k}
#check {n : ℤ // ∃ k, n = 2 * k}
#check ℤ
variables (C : set ℤ)
#check {n ∈ C | ∃ (k : ℤ), n = 2 * k}
#check {n : ℤ | n ∈ C ∧ ∃ (k : ℤ), n = 2 * k}
#check {x ∈ A | x = x}
#check {y | y ∈ A}
#check set_of_and
#check set_of_or

example : {n ∈ C | ∃ (k : ℤ), n = 2 * k} = {n : ℤ | n ∈ C ∧ ∃ (k : ℤ), n = 2 * k} := begin
  refl,
end


/- Lemma
Zeige.
-/
example {X : Type*} {A B : set X} : true :=
begin
  trivial,
end
