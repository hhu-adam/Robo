import Game.Metadata

World "Function"
Level 8

Title "Section"


Introduction
"
A function `g : B → A` is a right inverse of a function `f : A → B` if `f ∘ g = id`.

"

open Function


Statement (f g : ℤ × ℤ → ℤ × ℤ) (hf : ∀ m n, f (m , n) = (m + n , m + 2 * n))
    (hg : RightInverse g f) :
    ∀ x y,  g (x , y) = (2 * x - y , y - x) := by
  intro x y
  simp [Prod.eq_iff_fst_eq_snd_eq]
  set m := (g (x, y)).1
  set n := (g (x, y)).2
  have : (x, y) = (m + n, m + 2 * n) := by
    rw [← hf m n]
    rw [← hg (x, y)]
  injection this
  constructor
  · linear_combination (norm := ring_nf) 1 * snd_eq - 1 * fst_eq
    simp [fst_eq]
  · symm
    linear_combination 1* snd_eq - 1 * fst_eq



-- Statement (preamble := intro h) (g : ℤ × ℤ → ℤ × ℤ) :
--     let f : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (m + n, m + 2 * n)
--     (RightInverse f g) → g = fun (a, b) ↦ (2 * a - b, b - a) := by
  /-
  g : ℤ × ℤ → ℤ × ℤ
  f : ℤ × ℤ → ℤ × ℤ := fun x =>
    match x with
    | (m, n) => (m + n, m + 2 * n)
  h : Function.RightInverse f g
  ⊢ g = fun x =>
    match x with
    | (a, b) => (2 * a - b, b - a)
  -/
