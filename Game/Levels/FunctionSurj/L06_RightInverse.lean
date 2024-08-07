import Game.Metadata


World "FunctionSurj"
Level 6

Title "Right inverse"


Introduction
"

"

open Function


Statement (f g : ℤ × ℤ → ℤ × ℤ) (hf : ∀ m n, f (m , n) = (m + n , m + 2 * n))
    (hg : RightInverse g f) :
    ∀ x y,  g (x , y) = (2 * x - y , y - x) := by
  intro x y
  -- TODO: rw [Prod.eq_iff_fst_eq_snd_eq] does NOT work, so following step requires a hint
  simp [Prod.eq_iff_fst_eq_snd_eq]
  Hint "`set` funktioniert wie `let` aber setzt die neue Definition auch im Goal gleich ein."
  -- TODO: improve Hint
  set m := (g (x, y)).1
  set n := (g (x, y)).2
  have : (x, y) = (m + n, m + 2 * n) := by
    rw [← hf m n]
    rw [← hg (x, y)]
  injection this with fst_eq snd_eq
  constructor
  · linear_combination 1 * snd_eq - 2 * fst_eq
  · linear_combination 1 * fst_eq - 1* snd_eq

NewTactic set injection linear_combination
NewTheorem Prod.eq_iff_fst_eq_snd_eq
