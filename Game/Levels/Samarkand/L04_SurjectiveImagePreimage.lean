import Game.Levels.Samarkand.L03_SurjectiveRange


World "Samarkand"
Level 4
Title "" -- ""

open Set

/-
Introduction "
  **Arapuka**:  Könnt ihr mir vielleicht hiermit auch noch helfen?
  "
-/
Introduction "`INTRO` Intro Samarkand L04"

/---/
TheoremDoc Function.Surjective.image_preimage as "Surjective.image_preimage" in "Function"

namespace Function
Statement Surjective.image_preimage {A B : Type} {f : A → B} (hf : Surjective f) (T : Set B) :
f '' (f ⁻¹' T) = T := by
  /-
  Hint "
    **Du**:  Hatten wir das nicht eben schon?

    **Robo**:  Nein.  Vorhin hatten wir nur die Inklusion `image_preimage_subset`:
    ```
    f '' (f ⁻¹' T) ⊆ T
    ```
    Jetzt ist Gleichheit zu zeigen, aber unter der zusätzlichen Annahme, dass `f` surjektiv ist.
  "
  -/
  Hint "Remind `image_preimage_subset` and assumption that `f` surjectiv"
  ext b
  simp
  constructor
  · apply image_preimage_subset -- Lvl 1
  · intro hb
    obtain ⟨a, ha⟩ := hf b
    use a
    constructor
    · rw [ha]
      assumption
    · assumption

/-
Conclusion "
  **Arapuka**:  Ihr seid wirklich eine große Hilfe!
"
-/
Conclusion "`CONC` Conclusion Samarkand L04"
