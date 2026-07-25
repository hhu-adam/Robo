import Game.Levels.Samarkand.L03_SurjectiveRange


World "Samarkand"
Level 4
Title "" -- ""

open Function

/-
Introduction "
  **Arapuka**:  Könnt ihr mir vielleicht hiermit auch noch helfen?
  "
-/
Introduction "Intro Samarkand L04"

/---/
TheoremDoc Set.image_preimage_eq as "image_preimage_eq" in "Function"

namespace Set

Statement image_preimage_eq {A B : Type} {f : A → B} (T : Set B) (hf : Surjective f) :
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
  Hint "Remind `image_preimage_subset` i.e.
    ```
    f '' (f ⁻¹' T) ⊆ T
    ```
   and additional assumption that `f` surjectiv"
  ext b
  simp
  constructor
  · Hint "[Hint rips] remember `image_preimage_subset`"
    apply image_preimage_subset -- Lvl 1
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
Conclusion "Conclusion Samarkand L04"
