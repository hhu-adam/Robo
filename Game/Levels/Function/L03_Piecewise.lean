import Game.Metadata



World "Function"
Level 3

Title "Komposition"

Introduction
"
Endlich kommt ihr zur Bibliothek. Komischerweise stehen an der Tür
zwei Wächtern. Der eine zeigt euch ein Blatt mit

```
def f : ℚ → ℚ := fun x ↦ 5 * x
```

der andere eines mit

```
def g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0
```

und gibt dir ein Blatt mit einer einzelnen Zeile am oberen Ende.
"

open Set Function

namespace LevelFunction4

def f : ℚ → ℚ := fun x ↦ 5 * x
def g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0

Statement : f ∘ g = g ∘ f := by
  Hint "
    **Robo**: Schau mal, die beiden haben zwei Funktionen, eine davon mit stückweiser Definition.

    **Du**: Und ich soll zeigen, dass die beiden vertauschbar sind?

    **Robo**: Genau, am besten wählst du mit `funext x` ein beliebiges Element aus, und zeigst das
    dann für dieses."
  funext x
  Hint "
    **Du**: Ah und jetzt kann ich erst einmal `(g ∘ f) {x}` zu `g (f {x})` umschreiben?

    **Robo**: Mit `simp` klappt das."
  simp
  Hint "**Robo**: Jetzt würde ich einmal mit `unfold g` die Definition von `g` öffnen."
  unfold g
  Hint "
    **Robo**: Jetzt kannst du nämlich eine Fallunterscheidung
    machen, `by_cases h : 0 ≤ {x}`.

    **Du**: Damit krieg ich die Fälle `0 ≤ {x}` und `{x} < 0`?

    **Robo**: Genau! Oder präziser `0 ≤ {x}` und `¬(0 ≤ {x})`. Das ist nicht ganz das gleiche, und man
    könnte mit dem Lemma `not_le` zwischen `¬(0 ≤ {x})` und `0 < {x}` wechseln."
  by_cases h : 0 ≤ x
  · Hint "
      **Robo**: Um das ausrechnen zu können, brauchst du nicht nur `0 ≤ x` sondern auch noch
      eine neue Annahme `0 ≤ f x`.

      **Du**: Also `have h₂ : _`?"
    have h' : 0 ≤ f x
    · unfold f
      linarith
    rw [if_pos h]
    rw [if_pos h']
    unfold f
    ring
  · have h' : ¬ (0 ≤ f x)
    unfold f
    linarith
    rw [if_neg h]
    rw [if_neg h']
    unfold f
    ring

Conclusion
"
Zufrieden tauschen die beiden Wächter ihren Platz und geben so dabei den
Durchgang frei.
"

NewTactic funext simp_rw linarith

NewTheorem not_le if_pos if_neg
TheoremTab "Logic"

end LevelFunction4
