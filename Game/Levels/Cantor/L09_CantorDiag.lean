import Game.Metadata
import Game.Levels.Cantor.L08_CantorDiag_IsFixedPt

World "Cantor"
Level 9

Title ""

/-
Introduction
"
**Cantor**: Viel Glück!
"
-/
Introduction "`INTRO-1`Intro Cantor L09 - 1"

/-
Conclusion "**Du**: Jetzt möchte ich aber mit dieser generellen Form, die ursprüngliche
Aufgabe nochmals lösen."
-/
Conclusion "`CONC-1`Conclusion Cantor L09 - 1"

open Function Set

/---/
TheoremDoc cantor_diagonal as "cantor_diagonal" in "Function"

/-
Introduction "
  **Cantor**:  Passt auf!  Alles wird klar.  Hier ist der Schlüssel!
  Ihr müsst die Aussage von eben nur ein bisschen umformulieren.

  Er wirft euch einen neuen Zettel zu.
"
-/
Introduction "`INTRO-2`Intro Cantor L09 - 2"

/-
Conclusion "
  **Cantor**:  Bravo!
"
-/
Conclusion "`CONC-2`Conclusion Cantor L09 - 2"

Statement cantor_diagonal {A Y : Type} (f : A → A → Y) (hf : Surjective f) :
    ∀ s : Y → Y, Nonempty (fixedPoints s) := by
  /-
  Hint "
    **Du**:  Wir sollen unter bestimmten Annahmen zeigen, dass *jede* Selbstabbildung `s : {Y} → {Y}`
    einen Fixpunkt hat?  Gibt es nicht auf jeder Menge eine Selbstabbildung *ohne* Fixpunkte?
    Zum Beispiel $n ↦ n + 1$ auf $ℕ$ oder $ℝ$ …

    **Robo**:  … oder die nicht-triviale Permutation auf $\\\{0,1\\}$?

    Auch er ist anscheinend etwas verwirrt.

    **Robo**: Also, wenn `Y` nicht gerade die Einpunktmenge ist,
    sollte immer eine fixpunktfreie Selbstabbildung existieren.

    **Cantor**:  Na, das ist ja gerade der Witz!  Wartet ab!
    "
  -/
  Hint "The goal is that each self mapping `s : {Y} → {Y}` possess a fixed point.
  Does not every set have a self mapping without fixed points? E.g. $n ↦ n + 1$ in $ℕ$
  or $ℝ$ … or the non-trivial permutations in $\\\{0,1\\}$. Thought: if `Y` is not a set with
  a single element then there should be a fixed-point-free self mapping."
  intro s
  /-
  Hint (hidden := true) "**Cantor**: Ihr müsst natürlich irgendwie die
  Surjektivität von `{f}` ausnutzen. Aber ich hatte euch ja eben schon verraten,
  von welcher Abbildung `{A} → {Y}`  ihr ein Urbild betrachten müsst …

  **Robo** *(zu Dir)*: Mmm … verstehst du, was er meint?
  Natürlich könntest du jetzt eine Abbildung definieren mit
  ```
  let c : {A} → {Y} := fun a ↦ _
  ```
  und dann von dieser Abbildung `c` ein Urbild betrachten.
  Aber ich bin gerade etwas verloren.
  "
  -/
  Hint (hidden := true) "exploit the surjectivity of `{f}` somehow. It was already told
  which of mapping `{A} → {Y}` the preimage has to be considered. One could define ``` let c : {A} → {Y} := fun a ↦ _ ```
  and then observe the preimage of `c`."
  let c : A → Y := fun (a : A) ↦ s (f a a)
  -- Hint "**Cantor**: Gute Wahl!" -- will display irrespective of choice of c :(
  obtain ⟨a, ha⟩ := hf c
  use (f a a)
  unfold fixedPoints IsFixedPt
  simp
  apply congr_fun at ha
  specialize ha a
  --simp [c] at ha  -- optional
  symm
  assumption

TheoremTab "Function"
