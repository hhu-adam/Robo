import Game.Levels.Mono.L09_InjOfHasLeftInv

World "Mono"
Level 10

Title "" -- ""

Introduction ""

open Function Set

-- Could be done much earlier; needed as a have statement in the Boss level
-- Presumably needs hints!!
Statement {A B : Type} [hA : Nonempty A] (f : A → B ) : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b   := by
  Hint "
    **Du**:  Sind wir jetzt zurück auf Quantus?  Jedenfalls:  Es gibt ein `a` oder es gibt kein `a`, das sieht aus nach einer Tautologie.

    **Robo**:  Langsam!  Du musst die implizite Klammerung beachten. Ich schreib dir das mal mit mehr Klammern aus:
    ```
    ∀ b : B, ∃ a : A,
       ( f a = b   ∨   ¬ ∃ a' : A , f a' = b )
    ```
  "
  Hint (hidden := true) "
    **Robo**:  Vielleicht nimmst du dir als erstes mal mit `obtain` irgendein Element aus `A` her.
    Du weißt ja, dass es eins gibt.
  "
  obtain ⟨a₀⟩ := hA
  intro b
  Hint (hidden := true) "
    **Robo**:  Nun ja, du könntest mit `by_cases` eine Fallunterscheidung machen, ob denn nun `{b}` ein Urbild besitzt oder nicht.
  "
  by_cases hb : ∃ a' : A, f a' = b
  · obtain ⟨a,ha⟩ := hb
    use a
    left
    assumption
  use a₀
  right
  assumption
