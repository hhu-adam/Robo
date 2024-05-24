import Game.Metadata


World "FunctionBij"
Level 2

Title "Inverse"
Introduction
"
Eigentlich hast du nur beiläufig Robo gefragt, ob bijektiv nicht auch bedeute, dass
eine Inverse Funktion existiere. Jetzt steht ihr aber schon seit einer halben Stunde rum
und der Gelehrte möchte wissen, wie das den genau ginge.

Offensichtlich kennt er diese Aussage als `Function.bijective_iff_has_inverse` aus seinen Büchern,
aber er möchte, dass du ihm das hier und jetzt nochmals von Grund auf zeigst.
"

namespace Function

-- Note the fact that one sees `LeftInverse` but `Function.RightInverse` is because
  -- some Mathlib init-file defines `_root_.RightInverse`. mathlib4#11415 investigates this.

--TODO: `unfolding` at random places breaks all the hints...

Statement bijective_iff_has_inverse {A B : Type} (f : A → B) :
    Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f := by
  constructor
  · intro h
    Hint "
      **Robo**: Tipp. Teil doch `Bijective` mit `obtain ⟨hinj, hsurj⟩  := {h}` in
      `Injective` und `Surjective` auf!"
    obtain ⟨finj, fsurj⟩  := h
    Hint "
      **Du**: Ja was ist eigentlich die Inverse von `{f}`…?

      **Robo**: Hast du eine Idee?

      **Du**: Also von der Surjektivität weiss ich, dass für alle `y : B` ein Urbild `x : A` existiert.

      **Robo**: Mit `choose g hg using {fsurj} ` kannst du eine Funktion
      definieren, die `y` irgendein Urbild zuweist."
    choose g hg using fsurj
    Hint "
      something about the fact that ` ∀ (b : B), f (g b) = b` implies {g} is a right inverse of {f}. We use this in the next step to prove
      {g} is also a left inverse of {f}.
    "
    have hR : RightInverse g f := by
        exact hg
    use g
    constructor
    · Branch
        dsimp [Function.RightInverse]
        apply rightInverse_of_injective_of_leftInverse finj
        assumption
      Hint "
      **Robo**: Mit `dsimp` kannst du es ja etwas vereinfachen."
      dsimp [LeftInverse]
      Hint "
      **Robo**: fang mal mit `intro` an."
      intro x
      have : f (g (f x)) = f x  := by rw [hR]
      Branch
        apply finj at this
        assumption
      apply finj
      assumption
    · exact hR
  · intro h
    --obtain ⟨g, hL, hR⟩ := h
    Hint "**Robo**: Zerlege `{h}` noch soweit du kannst!"
    obtain ⟨g, h⟩ := h
    Hint "**Robo**: Das UND auch noch!"
    obtain ⟨hL, hR⟩  := h
    constructor
    Hint "
      **Robo**: Injektivität ist der schwierige Teil. Fang mal an mit `intro`."
    · intro a b eq
      rw [← hL a, ← hL b]
      Branch
        congr
      Hint (hidden := true) "
        **Du**: Wenn die Argumente `f a = f b` gleich sind, ist dann auch `g (f a) = g (f b)`,
        wie sag ich das?

      **Robo**: Also wenn du `f a = f b` hast, kannst du ja auch einfach damit umschreiben."
      rw [eq]
    · intro b
      use g b
      Hint (hidden := true) "
        **Robo**: Du kannst die `RightInverse`-Annahme einfach mit `rw`
        benutzen."
      rw [hR]


NewDefinition LeftInverse RightInverse
DisabledTheorem Function.bijective_iff_has_inverse
TheoremTab "Logic"


Conclusion
"
Endlich entkommt ihr der Bibliothek.

**Robo**: Da würden mich keine zehn Pferde nochmals hineinbringen!

**Du**: Von wegen Pferden, wie viele PS hat eigentlich unser Raumschiff?
"
