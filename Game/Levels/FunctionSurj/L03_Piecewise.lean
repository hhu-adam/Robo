import Game.Metadata


World "FunctionSurj"
Level 3

Title "Stückweise Definition"

Introduction
"
Endlich kommt ihr zur Bibliothek. Komischerweise stehen an der Tür
zwei Wächtern. Der eine hat ein `f` auf seiner Brustplatte, der andere
ein `g` eingraviert. Dieser gibt dir ein Blatt mit einer langen Zeilen am oberen Ende.
"

open Set Function

Statement :
    let f : ℚ → ℚ := fun x ↦ 5 * x
    let g : ℚ → ℚ := fun x ↦ if 0 ≤ x then 2*x else 0
    f ∘ g = g ∘ f := by
  Hint "
    **Robo**: Schau mal, die beiden haben zwei Funktionen, eine davon mit stückweiser Definition.

    **Du**: Also, ich soll zeigen, dass die beiden vertauschbar sind?

    **Robo**: Genau, am besten wählst du mit `funext x` ein beliebiges Element aus, und zeigst das
    dann für dieses."
  ext x
  Hint "
    **Du**: Ah und jetzt kann ich erst einmal `(g ∘ f) {x}` zu `g (f {x})` umschreiben?

    **Robo**: Mit `simp` klappt das."
  simp
  Hint (strict := true) "
    **Robo**: Jetzt kannst du nämlich eine Fallunterscheidung
    machen, `by_cases h : 0 ≤ {x}`.

    **Du**: Damit krieg ich die Fälle `0 ≤ {x}` und `0 > {x}`?

    **Robo**: Genau! Oder präziser `0 ≤ {x}` und `¬(0 ≤ {x})`. Das ist nicht ganz das gleiche,
    und man könnte mit dem Lemma `not_le` zwischen `¬(0 ≤ {x})` und `0 > {x}` wechseln."
  by_cases h : 0 ≤ x
  · Hint "**Du**: Jetzt muss ich wohl doch mal die Definitionen brauchen.

    **Robo**: Dann brauch mal `simp [f, g]`!"
    simp [f, g]
    Hint "
      **Robo**: Jetzt hast du `rw [if_pos {h}]` zur Verfügung um das if-then-else zu
      reduzieren."
    rw [if_pos h, if_pos h]
    ring
  · Hint (hidden := true) "**Robo**: Nochmals `simp [f, g]`."
    simp [f, g]
    Hint "**Du**: Ah und die Verneinung von `if_pos` ist sicher …"
    Hint (hidden := true) "**Robo**: `if_neg`, genau!"
    rw [if_neg h, if_neg h]

Conclusion
"
Zufrieden tauschen die beiden Wächter ihren Platz und geben so dabei den
Durchgang frei.
"

NewTactic ext
NewHiddenTactic funext

/--
Wenn `h : A` ein beweis der Aussage `A` ist, dann reduziert
`rw [if_pos h]` reduziert eine Aussage `if A then B else C` zu `B`.

Umgekehrt kann man `if_neg` verwenden wenn `h : ¬ A`.
-/
TheoremDoc if_pos as "if_pos" in "Logic"

/--
Wenn `h : ¬ A` ein Beweis ist, dass Aussage `A` falsch ist, dann reduziert
`rw [if_neg h]` eine Aussage `if A then B else C` zu `C`.

Umgekehrt kann man `if_pos` verwenden wenn `h : A`.
-/
TheoremDoc if_neg as "if_neg" in "Logic"

NewTheorem if_pos if_neg
TheoremTab "Logic"
