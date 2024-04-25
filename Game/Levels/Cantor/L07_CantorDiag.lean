import Game.Metadata
import Game.Levels.Cantor.L06_idempotent

World "Cantor"
Level 7

Title "Diagonalargument"

Introduction
"
**Cantor**: Genug gerätselt, jetzt aber zum Diagonalargument. Wir hatten doch
die Menge `C := { a | a ∉ f a }` angeschaut, und dann bewiesen dass diese kein Urbild unter `f`
haben kann.

Aber eine Menge `X : Set A` kann ich auch mit dem Prädikat `X' : A → Prop` gleichsetzen, dann
wäre mein `C` von vorhin stattdessen `fun (a : A) ↦ ¬ (f a a)`.

**Du**: Ich verstehe, dann ist `f : A → A → Prop` und mit `f a a` schauen wir uns sozusagen
die Diagonale an.

**Cantor**: Und dann statt `Prop` schauen wir ein beliebiges `Y` an und anstatt `¬(·)` nehmen
wir ein allgemeines `s : Y → Y`!

**Robo*: Übrigens, in Lean ist `Set A` tatsächlich explizit als `A → Prop` definiert,
diese \"Gleichsetzung\" ist also sozusagen die Definition.
"

Conclusion "**Du**: Jetzt möchte ich aber mit dieser generellen Form, die ursprüngliche
Aufgabe nochmals lösen."

open Function Set

Statement cantor_diagonal (f : A → A → Y) (hsurj : Surjective f) (s : Y → Y) :
    ∃ x, IsFixedPt s x := by
  Hint "**Cantor**: Also anstatt `C := \{ a | a ∉ f a }` braucht ihr jetzt
  `let c : A → Y := fun (a : A) ↦ s (f a a)`"
  let c : A → Y := fun (a : A) ↦ s (f a a)
  Hint "**Cantor**: Und gleich noch einen Tipp. Irgendwann hilft es, wenn man
  das Hilfslemma `have h : ∀ x, s (f x x) = c x` zeigt!"
  have h : ∀ x, s (f x x) = c x
  · Hint "**Du**: Dann mache ich mich mal an das Hilfslemma!"
    intro b
    unfold_let c
    rfl
  rcases hsurj c with ⟨y, hy⟩
  use (f y y)
  unfold IsFixedPt

  rw [h]
  rw [hy]

TheoremTab "Function"

-- theorem cantor_diagonal' (f : A → A → Y) (hsurj : Surjective f) :
--     ∀ (s : Y → Y), Nonempty (fixedPoints s) :=
--   by
--     intro s
--     let g : A → Y := fun (a : A) ↦ s (f a a)   --s ∘ f ∘ (δ A)
--     obtain ⟨a, ha⟩ := hsurj g
--     have : g a = s (f a a) := by rfl
--     use (f a a)
--     rw [mem_fixedPoints_iff]
--     rw [← this]
--     symm
--     apply congr_fun ha
--     -- rw [ha]
