import Game.Metadata


World "FunctionInj"
Level 5

Title "Monotone Funktionen"

Introduction
"
Sofort hakt die ältere Gestalt nach:
"

open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n^3 + (n + 3)
    Injective f := by
  Hint "
    **Du**: Hmm, das ist etwas schwieriger…

    **Robo**: Aber ich hab einen Trick auf Lager:
    Das Lemma `StrictMono.injective` sagt, dass jede strikt monotone Funktion injektive ist,
    und ich habe das Gefühl Monotonie ist hier einfacher zu zeigen."
  Hint (hidden := true) "**Robo**: `apply` ist wonach du suchst."
  Branch
    intro a b
    Hint "**Robo**: Ich glaube, dieser Weg ist zu steinig. Fang doch nochmals von vorne an!"
    intro ha
    Hint "**Robo**: Ich glaube, dieser Weg ist zu steinig. Fang doch nochmals von vorne an!"
  apply StrictMono.injective
  Hint "
    **Du**: Jetzt möchte ich strikte Monotonie von `n ^ 3` und `n + 3` separat zeigen,
    schliesslich scheint es mir als wär das zweite wieder einfach.

    **Robo**: Dafür hab ich `StrictMono.add` bereit!"
  apply StrictMono.add
  · Hint "**Du**: Hmm, darauf hab ich jetzt wenig Lust. Gibt's dafür auch was? Das gilt ja nur
      wenn der Exponent ungerade ist.

      **Robo**: Du könntest mal `Odd.strictMono_pow` versuchen…"
    apply Odd.strictMono_pow
    Hint (hidden := true) "**Du**: Ist das nicht ne Trivialität? Warte mal!"
    trivial
  · Hint "**Du**: Ha! Und dieser Teil funktioniert sicher gleich wie Injektivität vorhin!"
    Hint (hidden := true) "
      **Du**: oder …?

      **Robo**: Doch, doch. Schau mal mit `unfold` hinein in die Definition.
    "
    intro a b
    simp

/-- Dieses Lemma sagt `StrictMono f → Injective f`. -/
TheoremDoc StrictMono.injective as "StrictMono.injective" in "Function"

/-- Für ungerades `n` is `x ↦ x ^ n` strikt monoton.

*Bemerkung*: Das Lemma ist im namespace `Odd`, damit man `hn.strictMono_pow` für den
Beweis `hn : Odd n` schreiben könnte. -/
TheoremDoc Odd.strictMono_pow as "Odd.strictMono_pow" in "Function"

/-- Wenn `f,g` beide strikt monoton sind, dann ist es `f + g` auch. -/
TheoremDoc StrictMono.add as "StrictMono.add" in "Function"

NewTheorem StrictMono.injective StrictMono.add Odd.strictMono_pow
TheoremTab "Function"

Conclusion "
**Du**: Danke vielmals!

Und damit lässt das Wesen mitten im Gang stehen, wo es weiter über Injektivität nachdenkt.
"
