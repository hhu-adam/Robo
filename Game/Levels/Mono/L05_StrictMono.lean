import Game.Levels.Mono.L04_Diagonal

World "Mono"
Level 5

Title "" -- ""

Introduction ""

open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n^3 + (n + 3)
    Injective f := by
  /-
  Hint "
    **Du**: Hmm, das ist etwas schwieriger…

    **Robo**: Ich habe gerade auch keine gute Idee.

    Da hört ihr jemanden aus der Menge flüstern: `StrictMono` …

    **Robo**:  Ah, ja.  Es gibt da dieses Lemma `StrictMono.injective`:
    jede strikt monotone Abbildung ist injektiv.
    Und es gibt auch jede Menge Lemmas, mit denen man zeigen kann, dass Abbildungen monoton sind.
    Zum Beispiel:

    `StrictMono.add`  – die Summe zweier strikt monotoner Abbildungen ist wieder strikt monoton

    `Odd.strictMono_pow` – für ungerades `n` ist `x ↦ x ^ n` strikt monoton

     Wollen wir es damit einmal versuchen?"
  -/
  Hint "`StrictMono` is useful. `StrictMono.injective` says that each strictly monotone mapping
  is injective. To show that a mapping is monotone one can use e.g. `StrictMono.add` or `Odd.strictMono_pow`,
  which says that for uneven `n`, `x ↦ x ^ n` is monotone."
  -- Hint (hidden := true) "**Robo**: `apply` ist, wonach du suchst."
  Hint (hidden := true) "`apply` is what is looked for"
  Branch
    intro a b
    -- Hint "**Robo**: Ich glaube, dieser Weg ist zu steinig. Fang lieber nochmals von vorne an!"
    Hint "Try again from the beginning"
  Branch
    intro a b h
    -- Hint "**Robo**: Ich glaube, dieser Weg ist zu steinig. Fang lieber nochmals von vorne an!"
    Hint "Try again from the beginning"
  apply StrictMono.injective
  apply StrictMono.add
  · Branch
      have h_odd : Odd 3 := by
        decide
      --exact Odd.strictMono_pow h_odd
      exact h_odd.strictMono_pow
    apply Odd.strictMono_pow
    -- Hint (hidden := true) "**Du**: `Odd 3`. Ist das nicht eine Trivialität? Warte mal!"
    Hint (hidden := true) "`Odd 3` is trivial"
    decide
  · -- Hint "**Du**: Ha! Und dieser Teil geht jetzt vermutlich wieder ganz elementar."
    Hint "The next part is elementary"
    /-
    Hint (hidden := true) "
      **Du**: Oder …?

      **Robo**: Doch, doch. Schau mal mit `unfold` in die Definition von `StrictMono` hinein.
    "
    -/
    Hint "Use `unfold` to look into definition of `StrictMono`"
    intro a b
    simp

/--
`DOC` Every strictly monotonic mapping (between suitable domains and ranges) is injective.
-/
TheoremDoc StrictMono.injective as "StrictMono.injective" in "Function"

/-- Für ungerades `n` ist `x ↦ x ^ n` strikt monoton.

*Bemerkung*: Hat man `h_odd : Odd n` als Annahme, so kann man statt `Odd.strictMono_pow h_odd` auch einfach `h_odd.strictMono_pow` schreiben.
-/
TheoremDoc Odd.strictMono_pow as "Odd.strictMono_pow" in "Function"

/-- Sind `f` und `g` beide strikt monoton sind, so ist auch `f + g` strikt momonton. -/
TheoremDoc StrictMono.add as "StrictMono.add" in "Function"

NewDefinition StrictMono

NewTheorem StrictMono.injective StrictMono.add Odd.strictMono_pow
TheoremTab "Function"

Conclusion ""
