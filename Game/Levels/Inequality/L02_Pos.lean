import Game.Metadata


open Nat

World "Inequality"
Level 2

Title "Kleinergleich"

Introduction
"
**Lina**: Man muss zum Beispiel wissen, dass `n ≠ 0` für natürliche Zahlen nichts anderes
bedeutet als `0 < n`.

**Robo**: Und da gibts leider keinen Standard zu …

**Ritha**: Man kann das einfach mit `Nat.pos_iff_ne_zero` umschreiben. Aber wenn man neu hier
ist, sollte man das vielleicht noch einmal selbst beweisen?
"

Statement Nat.pos_iff_ne_zero (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  Hint "**Robo** (*flüsternd*): Wenn du ein bisschen schwere Maschinerie auffahren willst,
  um sie zu beeindrucken, hab ich was. Mach doch eine Fallunterscheidung ob `n` Null ist
  oder nicht!

  **Du** (*flüsternd*): Wer will hier wen beeindrucken?

  **Robo** (*laut und selbstsicher*): Wir fangen mit `rcases n` an!"
  rcases n
  Hint "**Du**: Hmm, das muss man doch vereinfachen können.

  **Robo** (*flüsternd*): Zweiter pompöser Auftritt: sag einfach `simp` und lass das alles
  automatisch geschehen."
  simp
  Hint "**Du**: Ah und jetzt falls `n ≠ 0`."
  Branch
    simp only [ne_eq, succ_ne_zero, not_false_iff, iff_true]
    Hint "**Robo**: Warte! Für den Rest zitieren wir einfach ein anderes Lemma: `Nat.suc_pos`."
    apply Nat.succ_pos
  Branch
    simp?
  constructor
  intro
  simp
  intro
  Hint "**Robo**: Warte! Für den Rest zitieren wir einfach ein anderes Lemma: `Nat.suc_pos`."
  apply Nat.succ_pos

/--
`simp` versucht alle Vereinfachungslemmas anzuwenden, die in der `mathlib` mit `@[simp]`
gekennzeichnet sind.

## Details

* `simp?` zeigt welche Lemmas verwendet wurden.
* `simp [my_lemma]` fügt zudem `my_lemma` temporär zur Menge der `simp`-Lemmas hinzu.
* ein `simp`, das nicht am Ende des Beweis steht sollte durch eine entsprechende
  `simp only [...]` Aussage ersetzt werden, um den Beweis stabiler zu machen.
-/
TacticDoc simp

NewTactic simp
NewTheorem Nat.succ_pos
DisabledTheorem Nat.pos_iff_ne_zero Nat.succ_pos'
TheoremTab "Nat"

Conclusion "**Du**: `simp` ist ja echt nicht schlecht …"
