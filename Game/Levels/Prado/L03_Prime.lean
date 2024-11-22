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
  Branch
    -- Marcus' solution
    have ha' : a ∣ p → a = 1 ∨ a = p
    · apply hp
    have ha'' : a = 1 ∨ a = p
    · apply ha'
      assumption
    obtain h1 | h2 := ha''
    linarith
    assumption
  Branch
    -- alternative to `specialize`
    have _hp := hp a ha
  specialize hp a ha
  obtain hp | hp := hp
  · Hint (hidden := true) "`linarith` kann den Widerspruch finden, der sich aus
    `{a} = 1` und `2 ≤ {a}` ergibt."
    linarith
  · assumption

/-- `specialize h a₁ a₂` ist äquivalent zu `have h := h a₁ a₂`; konkret ersetzt es eine Annahme
`h : ∀ m n, f m n` mit dem Spezialfall wo `a₁, a₂, …` für der Reihe nach für die
freien Variablen eingesetzt werden.

Falls man an mehreren Elementen separat spezialisieren möchte, sollte man stattdessen
`have` verwenden, da `specialize h a` die alte Annahme `h` überschreibt.

```
have ha := h a
have hb := h b
```

So kriegt man

```
h : ∀ m, f m
ha : f a
hb : f b
```

-/
TacticDoc specialize

NewTactic specialize
NewDefinition Nat.Prime
NewTheorem Nat.prime_def
TheoremTab "Nat"
