import Game.Levels.Samarkand.L02_ImageMap


World "Samarkand"
Level 3

Title "" -- "Range of Surjection"


Introduction ""

open Function Set

Statement {A B : Type} {f : A → B} : Surjective f ↔ range f = univ := by
  Hint "
    **Robo**:  Hier ist `range f` die gesamte Bildmenge von `f`:
    ```
      range f = \{f a | a : A}
              = \{  b | ∃ a, f a = b}
    ```
    Das ist also im wesentlichen eine andere Schreibweise für `f '' univ`.
    Um damit zu arbeiten, ist `mem_range` ganz nützlich:
    ```
    x ∈ range f ↔ ∃ a, f a = b
    ```
  "
  /-
  example : range f =  {b | ∃ a, f a = b} := by
    rfl

  example : range f =  {f a | a : A} := by
    rfl

  example : range f = f '' univ := by
    simp   -- (rfl fails)
  -/
  Hint (hidden := true)  "**Robo**: Ich würde mal mit `consturctor` anfangen."
  -- Branch
  --  symm
  --  exact eq_univ_iff_forall  -- not currently introduced anywhere (TODO?)
  constructor
  · intro hf
    Hint (hidden := true) "
      **Robo**: Ist nicht wieder eine Gleichheit von Mengen zu zeigen? Also `ext`.
      "
    ext b
    Branch
      tauto
    constructor
    · tauto
    · intro
      rw [mem_range] -- not necessary but desirable for the user.
      apply hf
  · intro h
    intro b
    --Branch
    --  simpa [← h] using mem_univ b -- simpa tactic has not been introduced
    rw [← mem_range]
    rw [h]
    tauto

NewDefinition Set.range

/---/
TheoremDoc Set.mem_range as "mem_range" in "Function"

NewTheorem Set.mem_range

Conclusion "
  **Arapuka**:  Auch schön.

  **Robo**:  Hast du eigentlich den ganzen Planeten hier bemalt?

  **Arapuka**:  Nein.  Das ist eine Aufgabe für Generationen.
  Die ersten Musterelement hat mein Urururur…opa geprägt.
  Ich weiß gar nicht genau, wie viele Generationen ich zurückgehen muss.
  Und erst recht nicht, woher das Urmuster kam.
"
