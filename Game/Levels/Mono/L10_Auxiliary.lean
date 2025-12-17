import Game.Levels.Mono.L09_InjOfHasLeftInv

World "Mono"
Level 10

Title ""

Introduction ""

open Function Set

-- Could be done much earlier; needed as a have statement in the Boss level
-- Presumably needs hints!!
Statement {A B : Type} [hA : Nonempty A] (f : A → B ) : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b   := by
  /-
  Hint "
    **Du**:  Sind wir jetzt zurück auf Quantus?  Jedenfalls:  Es gibt ein `a` oder es gibt kein `a`, das sieht aus nach einer Tautologie.

    **Robo**:  Langsam!  Du musst die implizite Klammerung beachten. Ich schreib dir das mal mit mehr Klammern aus:
    ```
    ∀ b : B, ∃ a : A,
       ( f a = b   ∨   ¬ ∃ a' : A , f a' = b )
    ```
  "
  -/
  Hint "Be careful with interpreting goal as 'there is `a` or there is no `a`'. Rewrite goal as ```
    ∀ b : B, ∃ a : A,
       ( f a = b   ∨   ¬ ∃ a' : A , f a' = b )
    ```"
  intro b
  /-
  Hint (hidden := true) "
    **Robo**:  Nun ja, du könntest mit `by_cases` eine Fallunterscheidung machen, ob denn nun `{b}` ein Urbild besitzt oder nicht.
  "
  -/
  Hint (hidden := true) "Try `by_cases` to see if `{b}` has preimage"
  by_cases hb : ∃ a' : A, f a' = b
  · obtain ⟨a,ha⟩ := hb
    use a
    left
    assumption
    /-
  · Hint (hidden := true) "
      **Robo**:  Du weißt ja zumindest, dass *irgendein* Element in `{A}` existiert.  Vielleicht „kontruierst“ du dir das einmal mit `obtain`.
    "
    -/
  · Hint (hidden := true) "Known that there exists some element in `{A}`. Try `obtain`"
    obtain ⟨a₀⟩ := hA
    use a₀
    right
    assumption
