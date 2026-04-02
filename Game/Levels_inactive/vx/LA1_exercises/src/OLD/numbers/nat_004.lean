-- Level name : Distributivität

-- begin hide
import numbers.nat_002b
-- end hide


/-
Distributivität heisst in Lean `add_mul : (a + b) * c = a * c + b * c`
und `mul_add : a * (b + c) = a * b + a * c`.

-/

/- Hint : repeat 
Normalerweise wird eine Taktik wie `rw mul_assoc` nur einmal ausgeführt.

Es kann aber durchaus sinnvoll sein, dies so oft zu machen wie es nur geht.

mit `repeat {rw mul_assoc}`, wiederholt Lean dies so oft wie möglich.
-/

/- Lemma : no-side-bar
Beweise.
-/
example (a b c : ℕ) : (a * a + a * b + a * b + b * b) = (a + b) * (b + a) :=
begin
  rw add_comm b a,
  rw add_mul,
  rw mul_add,
  rw mul_add,
  rw mul_comm b a,
  repeat {rw add_assoc},
end

/- Tactic : repeat
`repeat { TACTIC }` wiederholt die Taktic `TACTIC` so oft wie möglich.
-/

/- Axiom : add_mul
`(a + b) * c = a * c + b * c`.
-/

/- Axiom : mul_add
`a * (b + c) = a * b + a * c`.
-/
