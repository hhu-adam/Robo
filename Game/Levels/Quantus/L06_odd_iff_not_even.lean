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
        **Robo**:  Mit `odd_iff_not_even` kannst da `¬Odd` in `Even` verwandeln.
      "
    rw [← even_iff_not_odd] at h
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
      **Robo**:  Mit `odd_iff_not_even` kannst du `¬Even` in `Odd` verwandeln.
    "
    rw [← odd_iff_not_even] at h
    rw [Odd.neg_pow]
    rw [Even.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r+1
      rw [hr]
      ring
    · assumption

/-- Eine Zahl ist gerade wenn sie nicht ungerade ist. -/
TheoremDoc Nat.even_iff_not_odd as "even_iff_not_odd" in "ℕ"
#check  Nat.even_iff_not_odd

/-- Eine Zahl ist ungerade wenn sie nicht gerade ist. -/
TheoremDoc Nat.odd_iff_not_even as "odd_iff_not_even" in "ℕ"
-- It seems this has been renamed into `Nat.not_even_iff_odd` in newer versions of Mathlib,
-- and is now a simp lemma.

NewTheorem Nat.even_iff_not_odd Nat.odd_iff_not_even

Conclusion "Diesmal habt ihr die Formalosophinnen offenbar beeindruckt.  Sie nicken anerkennend.

Dann geht das Getuschel wieder los."
