import Game.Metadata



World "Function"
Level 3

Title "Komposition"

Introduction
"
Endlich kommt ihr zur Bibliothek. Komischerweise stehen an der Tür
zwei Wächtern. Der eine hat ein `f` auf seiner Brustplatte, der andere
ein `g` eingraviert. dieser gibt dir ein Blatt mit einer langen Zeilen am oberen Ende.
"

open Set Function

Statement :
    let f : ℚ → ℚ := fun x ↦ 5 * x
    let g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0
    f ∘ g = g ∘ f := by
  Hint "
    **Robo**: Schau mal, die beiden haben zwei Funktionen, eine davon mit stückweiser Definition."
  Hint (hidden := true) "
    **Du**: So viele Zeichen…

    **Robo**: Die beiden `let` solltest du mit `intro f g` in die Annahmen raufnehmen,
    dann ists etwas übersichtlicher!
    "
  intro f g
  Hint "
    **Du**: Also, ich soll zeigen, dass die beiden vertauschbar sind?

    **Robo**: Genau, am besten wählst du mit `funext x` ein beliebiges Element aus, und zeigst das
    dann für dieses."
  funext x
  Hint "
    **Du**: Ah und jetzt kann ich erst einmal `(g ∘ f) {x}` zu `g (f {x})` umschreiben?

    **Robo**: Mit `simp` klappt das."
  simp
  Hint "
    **Robo**: Jetzt kannst du nämlich eine Fallunterscheidung
    machen, `by_cases h : 0 ≤ {x}`.

    **Du**: Damit krieg ich die Fälle `0 ≤ {x}` und `{x} < 0`?

    **Robo**: Genau! Oder präziser `0 ≤ {x}` und `¬(0 ≤ {x})`. Das ist nicht ganz das gleiche,
    und man könnte mit dem Lemma `not_le` zwischen `¬(0 ≤ {x})` und `0 < {x}` wechseln."
  by_cases h : 0 ≤ x
  · Hint "
      **Robo**: Jetzt hast du `rw [if_pos {h}]` zur Verfügung um das if-then-else zu
      reduzieren."
    rw [if_pos h, if_pos h]
    ring
  · Hint "**Du**: Ah und die Verneinung von `if_pos` ist sicher …"
    Hint "**Robo**: `if_neg`, genau!"
    rw [if_neg h, if_neg h]

Conclusion
"
Zufrieden tauschen die beiden Wächter ihren Platz und geben so dabei den
Durchgang frei.
"

NewTactic funext simp_rw linarith

NewTheorem not_le if_pos if_neg
TheoremTab "Logic"
