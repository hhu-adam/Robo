import Game.Metadata
import Game.Levels.Prado.L02_EvenIff

namespace Nat

World "Prado"
Level 3

Title "Primzahlen"

Introduction
"
Eine Primzahl in den natürlichen Zahlen ist eine Zahl größergleich 2, wessen einzige Teiler
`1` und die Zahl selbst sind.

**Robo**: Wie du hier siehst ist `(hp : Prime p)` die Aussage, dass `p` eine Primzahl ist.

**Du**: Also ist dann `Prime p` genau diese Beschreibung?

**Robo**: Nein. Aus praktischen gründen ist `Prime p` dadurch definiert, dass `p`
\"irreduzibel\" ist, aber die Beschreibung oben, die heißt `prime_def`. Anstatt die Definition
zu unfolden, bist du immer mit `rw [prime_def] at hp` besser bedient!
"

-- TODO: there is a mathlib PR to ask for this renaming: #19255
alias _root_.Nat.prime_def := prime_def_lt''

Statement (a p : ℕ) (hp : Prime p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  Branch
    unfold Prime at hp
    Hint "Du solltest `Nat.Prime` nicht unfolden! Das macht alles nur schwieriger."
  Hint "**Robo**: Nah los, schreib mit `prime_def` die Annahme `{hp}` um!"
  rw [prime_def] at hp
  obtain ⟨hp₁, hp⟩ := hp
  specialize hp a ha
  obtain hp | hp := hp
  · Hint (hidden := true) "`linarith` kann den Widerspruch finden, der sich aus
    `{a} = 1` und `2 ≤ {a}` ergibt."
    linarith
  · assumption

NewDefinition Nat.Prime
NewTheorem Nat.prime_def
TheoremTab "Nat"
