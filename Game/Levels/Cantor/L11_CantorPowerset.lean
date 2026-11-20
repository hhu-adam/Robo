import Game.Metadata
import Game.Levels.Cantor.L10_SurjectiveMem

World "Cantor"
Level 11

Title ""

/-
**Cantor**:  Jetzt alles klar?
-/
Introduction "Intro Cantor L11"

/-
Conclusion "
  **Du**:  Ich weiß nicht, ob das wirklich einfacher war …
"
-/
Conclusion "Conclusion Cantor L11"

open Set Function

Statement {A : Type} : ¬ ∃ f : A → Set A, Surjective f := by
  Branch -- (This branch is not really needed, as it ends up with the same proof state as main branch.)
    by_contra h
    obtain ⟨f, hf⟩ := h
  push Not
  intro f
  by_contra hf
  /-
  **Du**: Also hier jetzt `cantor_diagonal` verwenden?

  **Robo**: Erst übersetzen, mit `surjective_mem_of_surjective`.
  -/
  Hint (hidden := true) "[Hint d92p1] Use `cantor_diagonal` now? First translate with
  `surjective_mem_of_surjective`."
  Branch
    clear hf
    let _C := { a | a ∉ f a }
    /-
    Hint "**Cantor**: Nein, nein! Wir wollten doch
      mein schönes Theorem `cantor_diagonal` verwenden!"
    -/
    Hint "[Hint mhjv] Try `cantor_diagonal`"
  Branch
    specialize hf { a | a ∉ f a }
    /-
    Hint "**Cantor**: Nein, nein! Wir wollten doch
      mein schönes Theorem `cantor_diagonal` verwenden!"
    -/
    Hint "[Hint mhjv] Try `cantor_diagonal`"
  apply surjective_mem_of_surjective at hf  -- L10
  /-
  **Robo**:  Jetzt ist `{hf}` eine Aussage über eine Abbildung `{A} → {A} → Prop`.
  -/
  Hint "[Hint u9e76] Now `{hf}` is about a map `{A} → {A} → Prop`."
  apply cantor_diagonal at hf  -- L09
  -- now see L05
  /-
  **Cantor**: Hatte ihr euch nicht schon überlegt, dass `¬ .` keine Fixpunkte hat?"
  -/
  Hint (hidden := true) "Does `¬ .` have no fixed points?"
  specialize hf (¬ .) -- or specialize h Not -- or specializa h (fun A ↦ ¬ A)
  obtain ⟨a, hA⟩ := hf
  unfold fixedPoints IsFixedPt at hA
  simp at hA

  DisabledTactic by_cases
