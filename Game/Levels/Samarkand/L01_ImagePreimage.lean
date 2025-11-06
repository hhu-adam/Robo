import Game.Metadata

open Set

World "Samarkand"
Level 1
Title "" -- "Bild/Urbild"


/-
Introduction "
**Arapuka**:  Es gibt da auch ein paar Dinge, über die ich schon lange nachdenke.
Vielleicht könntet ihr mir ja helfen.  Zum Beispiel: …

Sie diktiert euch eine Aussage. Robo schreibt sie auf.
"
-/
Introduction "`INTRO` Intro Samarkand L01"

/---/
TheoremDoc Set.image_preimage_subset as "image_preimage_subset" in "Set"

namespace Set

Statement image_preimage_subset {A B : Type} (f : A → B) (T : Set B) :
    f '' (f ⁻¹' T) ⊆ T := by
  /-
  Hint "
    **Robo**:  Die Notation hier muss ich dir, glaube ich, erklären.
    Gegeben ist offenbar eine Abbildung `f : A → B`.
    Für eine Teilmenge `S` von `A` ist
    ```
    f '' S = \{f a | a ∈ S}
           = \{b | ∃ a ∈ S, f a = b}
    ```
    ihr Bild unter `f`.  Und für eine Teilmenge `T` von `B` ist
    ```
    f ⁻¹' T = \{ a | f a ∈ T}
    ```
    ihr Urbild unter `f`."
  -/
  Hint "Explain statement: given `f : A → B` for subset `S` of `A`
    ```
    f '' S = \{f a | a ∈ S}
           = \{b | ∃ a ∈ S, f a = b}
    ```
    is the image over `f`. For subset `T` of `B`
    ```
    f ⁻¹' T = \{ a | f a ∈ T}
    ```
    is the pre-image over `f`,
    "

/- This is literally true:
example : f '' S = { f a | a ∈ S} := by
  rfl

example : f ⁻¹' T = { a | f a ∈ T} := by
  rfl
--/
  /-
  Hint (hidden := true) "
    **Robo:** Um eine Inklusion zu zeigen, nimmst du dir ein Element aus der linken Seite und zeigst, dass es in der rechten liegt.
    Also fang doch mal mit `intro b` an.
    "
  -/
  Hint (hidden := true) "Explain inclusion. Try `intro b`"
  intro b
  intro hb
  /-
  Hint (hidden := true) "
    **Robo**:  Um die Annahme `{hb}` in einen elementareren Ausdruck zu überführen, könntest du `simp` anwenden.
  "
  -/
  Hint (hidden := true) "Transform `{hb}` by using `simp`"
  simp at hb
  obtain ⟨a, ha₁, ha₂⟩ := hb
  rw [ha₂] at ha₁
  assumption

NewDefinition Set.fimage Set.fpreimage

/-
Conclusion "**Arapuka**: Schön."
-/

Conclusion "`CONC` Conclusion Samarkand L01"
