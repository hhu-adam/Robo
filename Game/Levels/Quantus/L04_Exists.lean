import Game.Metadata

World "Quantus"
Level 4

Title "" -- "Gerade/Ungerade"

/-
Introduction
"
Die Rufe „Even“ und „Odd“ aus der Menge sind noch lange nicht verstummt, deshalb
zeigt dir Robo nochmals die Definitionen:

```
def Even (n : ℕ) : Prop := ∃ r, n = r + r
```

und

```
def Odd (n : ℕ) : Prop := ∃ r, n = 2 * r + 1
```

Damit erhaltet ihr auch ein weiteres Blatt:
"
-/
Introduction "Intro Quantus L04: Show defintion
```
def Even (n : ℕ) : Prop := ∃ r, n = r + r
```

and

```
def Odd (n : ℕ) : Prop := ∃ r, n = 2 * r + 1
```
"

open Nat

/-- Das Quadrat einer geraden Zahl ist gerade. -/
TheoremDoc Nat.even_square as "even_square" in "ℕ"

Statement Nat.even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  /-
  Hint "
    **Robo**: Wie du oben siehst, ist `Even {n}` dadurch definiert,
    dass ein `r` existiert so dass `r + r = {n}` ist. Am besten
    öffnest du diese Definition mit `unfold Even at *` einmal.
    Dann siehst du besser, was los ist.

    **Du**: Was ist mit `decide`?

    **Robo**: `decide` wird nicht funktionieren, da `{n}` keine konkrete sondern
    eine beliebige Zahl ist. Da musst du schon etwas Arbeit leisten!"
  -/
  Hint "Explain definition of `Even {n}` by `r` using `r + r = {n}`. Look up definition by `unfold Even at *`.
  `decide` might be considered but `decide` does not work, because of `{n}` arbitrary."
  Branch
    unfold Even
    -- Hint "
    --   Robo**: Am besten machst du auch noch `unfold Even at h`, damit du verstehst, was los ist."
    Hint "Try `unfold Even at h`"
  unfold Even at *
  Branch
    clear h -- we do that so the hint gets displayed regardless of the presence of additional hyps.
    use n^2/2
    /-
    Hint "Ein verwirrtes murmeln geht durch die Menge.

    **Du**: Warte mal, wieso ist `{n} ^ 2 / 2` überhaupt wieder eine natürliche Zahl?

    **Robo**: Division auf `ℕ` wird in Lean immer abgerundet. Für `{n} = 1` steht da also

    ```
    1 ^ 2 = (1 ^ 2) / 2 + (1 ^ 2) / 2
    ```

    was ausgerechnet `1 = 1 / 2 + 1 / 2 = 0 + 0` ist, du bist also auf dem Holzweg!
    "
    -/
    Hint "`{n} ^ 2 / 2` is a natural number because division over `ℕ` in Lean is always rounded down.
    For `{n} = 1` that means
    ```
    1 ^ 2 = (1 ^ 2) / 2 + (1 ^ 2) / 2
    ```
    which is  `1 = 1 / 2 + 1 / 2 = 0 + 0`.
    "
  /-
  Hint "
    **Du**: Also von `{h}` weiß ich jetzt, dass ein `s` existiert, so dass `s + s = {n}` …

    **Robo**: Mit `choose s hs using {h}` kannst du dieses `s` tatsächlich einführen."
  -/
  Hint "Explain that from `{h}` follow that there is `s` such that `s + s = {n}`. Try `choose s hs using {h}`
  to introduce `s`."
  choose s hs using h
  /-
  Hint "
    **Du**: Und jetzt muss ich eine passende Zahl `r` finden, so dass `n ^ 2 = r + r`?

    **Robo**: Genau. Wenn du willst, kannst du dir diese Zahl erst einmal mit
    `let r := …`  zurechtlegen."
  -/
  Hint "Find `r` such that `n ^ 2 = r + r`. Try `let r := …`"
  Branch
    rw [hs]
    -- Hint "**Robo**: Das geht auch, jetzt musst du der wirlich eine Zahl überlegen."
    Hint "Set number"
  let r := 2 * s^2
  /-
  Hint "
    **Robo**:  Die Zahl sieht gut aus!  Und jetzt sagst du einfach `use r`.
    Du hättest natürlich auch gleich `use 2 * s^2` sagen können.
  "
  -/
  Hint "Try `use r` or instead `use 2 * s^2`"
  use r
  /-
  Hint (hidden := true) "
    **Du**: Ah, und jetzt `ring`!

    **Robo**: Aber zuerst musst du noch mit
    `rw` `n` durch `{s} + {s}` ersetzen, da `ring` das sonst nicht weiß."
  -/
  Hint (hidden := true) "before using `ring`, use `rw` to replace `n` by `{s} + {s}`, because
  `ring` does not know otherwise."
  rw [hs]
  ring

NewTactic unfold choose «let»
NewHiddenTactic «using»
-- `let` is introduced here only to avoid dependency of Vieta on Euklid
--  Those are the first two planets that really need `let`,
--  and introducing `let` there will create dependencies of all later planets
--  on *both* of these!

NewDefinition Even Odd

-- Conclusion "Applaus!"
Conclusion "`CONC` Conclusion Quantus L04"
