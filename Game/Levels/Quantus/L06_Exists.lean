import Game.Metadata

World "Quantus"
Level 6

Title "Gerade/Ungerade"

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

open Nat

/-- Das Quadrat einer geraden Zahl ist gerade. -/
TheoremDoc Nat.even_square as "even_square" in "ℕ"

Statement Nat.even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  Hint "
    **Robo**: Wie du oben siehst, ist `Even {n}` dadurch definiert,
    dass ein `r` existiert so dass `r + r = {n}` ist. Am besten
    öffnest du diese Definition mit `unfold Even at *` einmal.
    Dann siehst du besser, was los ist.

    **Du**: Was ist mit `decide`?

    **Robo**: `decide` wird nicht funktionieren, da `{n}` keine konkrete sondern
    eine beliebige Zahl ist. Da musst du schon etwas Arbeit leisten!"
  Branch
    unfold Even
    Hint "
      Robo**: Am besten machst du auch noch `unfold Even at h`, damit du verstehst, was los ist."
  unfold Even at *
  Branch
    clear h -- we do that so the hint gets displayed regardless of the presence of additional hyps.
    use n^2/2
    Hint "Ein verwirrtes murmeln geht durch die Menge.

    **Du**: Warte mal, wieso ist `{n} ^ 2 / 2` überhaupt wieder eine natürliche Zahl?

    **Robo**: Division auf `ℕ` wird in Lean immer abgerundet. Für `{n} = 1` steht da also

    ```
    1 ^ 2 = (1 ^ 2) / 2 + (1 ^ 2) / 2
    ```

    was ausgerechnet `1 = 1 / 2 + 1 / 2 = 0 + 0` ist, du bist also auf dem Holzweg!
    "
  Hint "
    **Du**: Also von `{h}` weiß ich jetzt, dass ein `r` existiert, so dass `r + r = {n}` …

    **Robo**: Mit `obtain ⟨r, hr⟩ := {h}` kannst du dieses `r` tatsächlich einführen."
  obtain ⟨r, hr⟩ := h
  Hint "
    **Du**: Und jetzt muss ich eine passende Zahl finden, so dass `x + x = {n} ^ 2`?

    **Robo**: Genau. Und mit `use _` gibst du diese Zahl an."
  Hint (hidden := true) "
    **Robo**: Also sowas ähnliches wie `use 4 * {r} ^ 3`, aber ich kann
    dir leider nicht sagen, welche Zahl passt."
  Branch
    rw [hr]
    Hint "**Robo**: Das geht auch, jetzt musst du aber wirklich `use` verwenden."
    use 2 * r ^ 2
    Hint (hidden := true) "**Du**: Ah, und jetzt `ring`!"
    ring
  use 2 * r ^ 2
  Hint "
    **Du**: Ah, und jetzt `ring`!

    **Robo**: Aber zuerst musst du noch mit
    `rw` `n` durch `{r} + {r}` ersetzen, da `ring` das sonst nicht weiß."
  rw [hr]
  ring

NewTactic unfold use
NewDefinition Even Odd

Conclusion "Applaus!"
