import Game.Metadata

open Function Set

/- L05:
    only two lines, so don't need a name
-/
example : ¬ ∃ (P : Prop),  IsFixedPt (¬ .) P := by
  unfold IsFixedPt
  simp -- or tauto, but simp is better, because it can be applied "at h"

/- L06: … -/

/- L07:  planned to be used as `range_fixedPoints` for future planet on quotients;
         don't need a name for now
-/

example {A : Type} (f : A → A) (h : f ∘ f = f) :
    range f = fixedPoints f := by
  apply congr_fun at h
  rw [Subset.antisymm_iff]
  constructor
  · intro x hx
    obtain ⟨a, ha⟩ := hx
    rw [← ha]
    unfold fixedPoints IsFixedPt
    simp --or rw [mem_setOf]
    simp [comp_apply] at h
    rw [h]
  · intro x hx
    simp
    use x
    apply hx

/- L08*: don't give it a name, but rather *repeat* argument in next level -/
example {A Y : Type} {f : A → A → Y} {s : Y → Y}
     {a : A} (ha : f a = fun a' ↦ s (f a' a')) :
  IsFixedPt s (f a a) := by
  unfold IsFixedPt
  apply congr_fun at ha
  specialize ha a
  rw [← ha]

/- L09: pre-Boss -/
theorem cantor_diagonal {A Y : Type} (f : A → A → Y) (hsurj : Surjective f) :
    ∀ s : Y → Y, Nonempty (fixedPoints s) := by
  intro s
  let c : A → Y := fun (a : A) ↦ s (f a a)
  obtain ⟨a, ha⟩ := hsurj c
  --unfold Set.Nonempty  -- optional
  use (f a a)
  -- from here, repeat **L08**
  unfold fixedPoints IsFixedPt
  simp
  apply congr_fun at ha
  specialize ha a
  simp [c] at ha  -- optional
  symm
  assumption

/- L10 -/
example {A : Type} : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  by_contra h
  apply cantor_diagonal at h -- **L09**  (6 lines + 3 lines form L08)
  -- now see **L05**
  specialize h (fun A ↦ ¬ A) -- or specialize h Not
  obtain ⟨a, hA⟩ := h
  unfold fixedPoints IsFixedPt at hA
  simp at hA

/- L11 -/
open Nat
example (f : ℕ → ℕ → ℕ) : ∃ (g : ℕ → ℕ), ∀ (n : ℕ), f n ≠ g := by
  have h : ¬ Surjective f := by
    intro h
    apply cantor_diagonal at h -- **L09**
    specialize h succ
    obtain ⟨n, hn⟩ := h
    unfold fixedPoints IsFixedPt at hn
    simp at hn
  unfold Surjective at h
  push_neg at h
  assumption
