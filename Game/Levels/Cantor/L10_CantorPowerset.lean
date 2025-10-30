import Game.Metadata
import Game.Levels.Cantor.L09_CantorDiag

World "Cantor"
Level 10

Title ""

/-
Introduction
"
**Cantor**: Und jetzt nehmt ihr dieses schöne Diagonalargument und zeigt noch einmal,
dass es keine surjektiven Abbildungen `A → Set A` gibt!
Ihr müsst nur `Set A` auffassen als `A → Prop`!

**Du**: Was?

**Robo**:  Eine Teilmenge `S : Set A` kann man mit der Abbildung
`A → Prop` identifizieren, die `a : A` auf die Aussage `a ∈ S` wirft.
Für Formalosophen ist das dasselbe.
"
-/
Introduction "Intro Cantor L10: Show that there are no surjective mappings `A → Set A` by interpreting
`Set A` as `A → Prop`. Sub set `S : Set A` can be seen as `A → Prop`, which casts `a : A` on statement `a ∈ S`"

/-
Conclusion "
  **Du**:  Ich weiß nicht, ob das wirklich einfacher war …
"
-/
Conclusion "`CONC`Conclusion Cantor L10"

open Set Function

Statement {A : Type} : ¬ ∃ f : A → Set A, Surjective f := by
  Branch -- (This branch is not really needed, as it ends up with the same proof state as main branch.)
    by_contra h
    obtain ⟨f, hf⟩ := h
    /-
    Hint (hidden := true) "
    **Du**: Also hier jetzt `cantor_diagonal` verwenden?

    **Robo**: Vermutlich, zum Beispiel mit `apply cantor_diagonal at {hf}`.
    "
    -/
    Hint (hidden := true) "Use `cantor_diagonal` as e.g. `apply cantor_diagonal at {hf}`"
  push_neg
  intro f
  by_contra hf
  /-
  Hint (hidden := true) "
    **Du**: Also hier jetzt `cantor_diagonal` verwenden?

    **Robo**: Vermutlich, zum Beispiel mit `apply cantor_diagonal at {hf}`.
  "
  -/
  Hint "Use `cantor_diagonal` as e.g. `apply cantor_diagonal at {hf}`"
  Branch
    clear hf
    let _C := { a | a ∉ f a }
    /-
    Hint "**Cantor**: Nein, nein! Wir wollten doch
      mein schönes Theorem `cantor_diagonal` verwenden!"
    -/
    Hint "Try `cantor_diagonal`"
  Branch
    specialize hf { a | a ∉ f a }
    /-
    Hint "**Cantor**: Nein, nein! Wir wollten doch
      mein schönes Theorem `cantor_diagonal` verwenden!"
    -/
    Hint "Try `cantor_diagonal`"
  apply cantor_diagonal at hf  -- L09
  -- now see L05
  /-
  Hint (hidden := true) (strict := true) "
  **Cantor**: Hatte ihr euch nicht schon überlegt, dass `¬ .` keine Fixpunkte hat?"
  -/
  Hint "Does `¬ .` have no fixed points?"
  specialize hf (¬ .) -- or specialize h Not -- or specializa h (fun A ↦ ¬ A)
  obtain ⟨a, hA⟩ := hf
  unfold fixedPoints IsFixedPt at hA
  simp at hA

  DisabledTactic by_cases
