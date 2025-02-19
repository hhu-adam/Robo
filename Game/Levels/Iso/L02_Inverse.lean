import Game.Metadata


World "Iso"
Level 2

Title "" -- "Inverse"
Introduction
"
**Isosoph**:  … und zur Hauptsache kommen.
"

namespace Function


--TODO: `unfolding` at random places breaks all the hints...

/---/
TheoremDoc Function.bijective_iff_has_inverse as "bijective_iff_has_inverse" in "Function"

Statement bijective_iff_has_inverse {A B : Type} (f : A → B) :
    Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f := by
  Hint "**Du**:  Eine Abbildung ist genau dann bijektiv, wenn eine zur ihr inverse Abbildung existiert.
  Das ist ja im Wesentlich dass, was wir auf Epo und Mono schon gezeigt hatten.
  Hattest du dir die Aussagen abgespeichert?

  **Robo**:  Schon, aber ich glaube, wenn wir die hier auspacken, gehen die Augenbrauen nach oben.
  Lass uns lieber scharf nachdenken und uns erinnern, wie das ging.
  "
  constructor
  · intro h
    Hint (hidden := true)"
      **Robo**: Teil doch erst einmal `Bijective` mit `obtain ⟨hinj, hsurj⟩  := {h}` in
      `Injective` und `Surjective` auf!"
    obtain ⟨finj, fsurj⟩  := h
    Hint (hidden := true)"
      **Robo**: Aus der Surjektivität weisst du, dass jedes `y : B` ein Urbild `x : A` hat.
      Kannst du daraus nicht mit `choose` eine Umkehrabbildung konstruieren?"
    choose g hg using fsurj
    Hint "
      Zeig am besten erst einmal, dass `{g}` ein Rechtsinverses von `{f}` ist,
      also zum Beispiel `have hR : RightInverse {g} {f}`
    "
    have hR : RightInverse g f := by
      assumption
    use g
    constructor
    · --Branch
      --  apply rightInverse_of_injective_of_leftInverse finj  -- das ist Mono, L08, aber wir haben das Lemma nicht gespeichert.
      --  assumption
      Hint (hidden := true)"**Robo**: Mit `simp [LeftInverse]` kannst du dir das Beweisziel etwas vereinfachen."
      simp [LeftInverse]
      Hint (hidden := true) "**Robo**: Warum beginnst du nicht mit `intro`?"
      intro x
      have : f (g (f x)) = f x  := by rw [hR]
      Branch
        apply finj at this
        assumption
      apply finj
      assumption
    · assumption
  · intro h
    --obtain ⟨g, hL, hR⟩ := h
    Hint (hidden := true) "**Robo**: Zerlege `{h}` noch soweit du kannst!"
    obtain ⟨g, h⟩ := h
    Hint (hidden := true) "**Robo**: Das UND auch noch!"
    obtain ⟨hL, hR⟩  := h
    constructor
    Hint (hidden := true) "
      **Robo**: Injektivität ist der schwierigere Teil. Fang mal an mit `intro`."
    · intro a b eq
      rw [← hL a, ← hL b]
      Branch
        congr
      Hint (hidden := true) "
        **Du**: Wenn die Argumente `f a = f b` gleich sind, ist auch `g (f a) = g (f b)` –
        wie sag ich das nochmal?

      **Robo**: Also, wenn du `f a = f b` hast, kannst du ja auch einfach `rw` benutzen."
      rw [eq]
    · intro b
      use g b
      Hint (hidden := true) "
        **Robo**: Hier kannst du die `RightInverse`-Annahme mit `rw` benutzen."
      rw [hR]


TheoremTab "Logic"
DisabledTheorem Function.injective_iff_hasLeftInverse Function.surjective_iff_hasRightInverse

Conclusion
"
Die Isosophen zeigen sich sehr zufrieden.

**Robo**:  Können wir jetzt nochmal … kapseln?

**Isosoph**:  Klar!  Aber immer schön der Reihe nach.
Seit wir die Kapseln in beide Richtungen benutzen, häufen sich wieder die Unfälle.

Robo fährt noch dreimal hin und zurück.  Dann fliegt ihr weiter.
"
