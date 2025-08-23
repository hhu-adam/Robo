import Game.Metadata

World "Quantus"
Level 6

Title ""

Introduction "Sofort taucht das nächste Blatt auf.
Es scheint, als hätten sie sich diesmal auf einen Kompromiss geeignet."

open Nat

Statement (i : ℕ): (-1 : ℤ)^i  + (-1 : ℤ)^(i+1) = 0 := by
  Hint (hidden := true) "
    **Du**:  Ich glaube, ich würd gern eine Fallunterscheidung machen, ob `i` gerade oder ungerade ist.

    **Robo**:  Dann mach das doch – zum Beispiel mit `by_cases h : Even i`.
  "
  Branch
    by_cases h : Odd i
    swap  -- TODO: check whether this triggers in the correct moment
    Hint "
        **Robo**:  Mit `not_even_iff_odd` kannst da `¬Odd` in `Even` verwandeln.
      "
    rw [not_odd_iff_even] at h
  by_cases h : Even i
  · rw [Even.neg_pow]
    rw [Odd.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r
      rw [hr]
      ring
    · assumption
  · Hint "
      **Robo**:  Mit `not_even_iff_odd` kannst du `¬Even` in `Odd` verwandeln.
    "
    rw [not_even_iff_odd] at h
    rw [Odd.neg_pow]
    rw [Even.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r+1
      rw [hr]
      ring
    · assumption

/---/
TheoremDoc Nat.not_odd_iff_even as "not_odd_iff_even" in "ℕ"
#check  Nat.not_odd_iff_even

/---/
TheoremDoc Nat.not_even_iff_odd as "not_even_iff_odd" in "ℕ"
-- It seems this has been renamed into `Nat.not_even_iff_odd` in newer versions of mathlib,
-- and is now a simp lemma.

NewTheorem Nat.not_odd_iff_even Nat.not_even_iff_odd

Conclusion "Diesmal habt ihr die Formalosophinnen offenbar beeindruckt.  Sie nicken anerkennend.

Dann geht das Getuschel wieder los."
