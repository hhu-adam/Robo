-- Level name : Kommutativität, Assoziativität

-- begin hide
import numbers.nat_002b
-- end hide

/-
Also nächstes schauen wir uns Kommutativität und Assotiativität an.
`add_assoc : a + b + c = a + (b + c)` und `add_comm : a + b = b + a`.

Du kannst auch wieder mit `rw ←add_assoc` dieses rückwärts anwenden, und mit
`add_comm a b` oder `add_assoc _ _ b` kannst du spezifizieren, wo genau du diese
anwenden willst. Z.B. sucht der zweite Befehl nach einem Term `_ + _ + b`, wobei `_`
Platzhalter sind.

-/

/- Lemma : no-side-bar
Zeige.
-/
example (a b c : ℕ) : a + b + b + c = a + c + b + b :=
begin
  rw add_comm,
  rw ←add_assoc,
  rw ←add_assoc,
  rw add_comm c,
end

/- Axiom : add_assoc
`a + b + c = a + (b + c)`.
-/

/- Axiom : mul_assoc
`a * b * c = a * (b * c)`.
-/

/- Axiom : add_comm
`a + b = b + a`.
-/

/- Axiom : mul_comm
`a * b = b * a`.
-/
