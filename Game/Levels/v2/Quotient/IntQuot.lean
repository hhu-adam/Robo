import Mathlib

instance intQuotRel : Setoid (ℕ × ℕ) where
  r a b := a.1 + b.2 = b.1 + a.2
  iseqv := {
    refl := fun x => rfl
    symm := fun {x y} h => Eq.symm h
    trans := fun {x y z} hxy hyz => by
      apply add_right_cancel (b := y.1 + y.2)
      trans (x.1 + y.2) + (y.1 + z.2)
      · ring
      · rw [hxy, hyz]
        ring
  }

def myInt := Quotient intQuotRel

def g : ℕ × ℕ → ℕ := fun (a, b) => a - b

theorem g_welldef (x y : ℕ × ℕ) (h : x ≈ y) : g x = g y := by
  simp [g]
  change x.1 + y.2 = y.1 + x.2 at h
  sorry -- not so simple argument

def g' : myInt → ℕ := Quotient.lift g g_welldef
