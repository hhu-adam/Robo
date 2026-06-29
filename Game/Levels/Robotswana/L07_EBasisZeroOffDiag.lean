import Game.Levels.Robotswana.L06_EBasisEqOnDiag

World "Robotswana"
Level 7

Title ""

Introduction "intro Robotswana L07: Introduce new consideration for `E i j`: do not consider `E i j` with i ≠ j"

Conclusion "Conclusion Robotswana L07"

open Nat Matrix

/---/
TheoremDoc Matrix.zero_on_offDiag_ebasis as "zero_on_offDiag_ebasis" in "Matrix"

Statement Matrix.zero_on_offDiag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    {i j : Fin n} (h_ne : i ≠ j) (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    f (E i j) = 0 := by
  Branch
    rw [← E.mul_same i j j]
    rw [h₁]
    rw [E.mul_of_ne] -- (***)
    -- The first goal and its associated proof state
    -- at this point of a correct solution
    -- match the first goal and proof state
    -- of an incorrect attempt further below!
  Branch
    /-
    Hint "**Robo**: Wie könnten wir denn hier `{h₁}` verwenden?

    **Du**: Wie wär's, wenn wir diesmal `E i j` als Produkt `E i j * E j j` schreiben?

    **Robo**:  Wieso gerade so?

    **Du**: Wenn ich in diesem Produkt die Faktoren vertausche, erhalte ich Null!  Hatten wir doch auch schon, `E.mul_of_ne` oder so etwas."
    -/
    Hint "Use `{h₁}` by writing `E i j` as `E i j * E j j`. Remind `E.mul_of_ne`"
    -- Hint (hidden := true) "**Robo*: Wie du meinst. Dann probier doch am besten `trans f (E i j * E j j)`."
    Hint "[Hint plnk] Try `trans f (E i j * E j j)`"
    trans f (E i j * E j j)
    /-
    · Hint (hidden := true) "**Du**: Ehm, das sehe ich einfach von der Definition.

      **Robo**: Vergiss nicht `unfold E`, oder sag `simp`, dass es die Definition von `E` benutzen soll (`simp [E]`)."
    -/
    · Hint (hidden := true) "Try `unfold E` or `simp` with `E` via `simp [E]`"
      simp [E]
    /-
    · Hint "**Robo**: Und hier wolltest du jetzt kommutieren?

      **Du**: Genau!"
    -/
    · Hint "[Robotswana.L07] Hint 1: Try commutating"
      Branch
        rw [E.mul_of_ne] -- (***)
        -- Would ideally like to already trigger a warning here, but
        -- first goal and proof state are identical to first proof
        -- reached in a correct solution (see (***) in first Branch above)
        simp
        -- Hint "**Robo**:  Oh. Das sieht falsch aus."
        Hint "[Robotswana.L07] Hint 2: Try rewriting with `h₁`"
      rw [h₁]
      rw [E.mul_of_ne] -- Lvl 2
      · simp
      · symm
        assumption
  specialize h₁ (E i j) (E j j)
  simp [E.mul_same] at h₁
  simp [E.mul_of_ne j j h_ne.symm] at h₁
  assumption


--NewTheorem Matrix.E.mul_of_ne
TheoremTab "Matrix"
