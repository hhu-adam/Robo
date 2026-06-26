import Game.Metadata

World "Babylon"
Level 4

Title ""

/-
Introduction
"
  Ihr wandert weiter von Turm zu Turm.  Schließlich bleibst du an einem Turm stehen,
  der dir seltsam vorkommt.  Nachdem ihr einmal um ihn herumgelaufen seid, weißt du auch, warum:
  Es fehlt ein Eingang.  Immerhin findet ihr eine Bodenplatte mit folgender Inschrift.
"
-/
Introduction "Intro Babylon L04"

open Finset FullGrind

Statement  (n : ℕ) (hn : 3 ≤ n) : ∑ i ∈ Icc 0 n, (i^3 - 3 * i^2 + 2*i : ℤ ) = ∑ i ∈ Icc 3 n, (i^3 - 3*i^2 + 2*i : ℤ) := by
  /-
  Hint "**Du**: Mal langsam.  Zu zeigen ist:

  $$
  \\sum_\{i=0}^\{n} (i^3 - 3 i^2 + 2 i)  = \\sum_\{i=3}^\{n} (i^3 - 3 i^2 + 2i)
  $$

  Vermutlich ist der Ausdruck in der Summe einfach $0$ für die ersten drei Werte von $i$ … ja, genau.
  Und wie formulier ich das jetzt?

  **Robo**: Du könntest `sum_subset` verwenden: ist `I₁ ⊆ I₂`,
  und verschwindet der Ausdruck in der Summe auf allen Element von `I₁`, die nicht in `I₂` liegen,
  so ist die Summe über `I₁` gleich der Summe über `I₂`.
  "
  -/
  Hint "Remind goal $$ \\sum_\{i=0}^\{n} (i^3 - 3 i^2 + 2 i)  = \\sum_\{i=3}^\{n} (i^3 - 3 i^2 + 2i) $$ with $0$ for the value in the sum for fist three $i$. Try `sum_subset`: If `I₁ ⊆ I₂` and term is disappearing for all elements in I₂ not in I₁, then the sum over `I₁` equals sum over `I₂`"
  Branch
    apply sum_subset
    -- Hint "**Robo**:  Nein, das sieht falschherum aus."
    Hint "Wrong order"
    -- Hint (hidden := true) "**Robo**:  Vertausch erst einmal mit `symm` die beiden Seiten der Gleichung."
    Hint (hidden := true) "[Hint rxjt] Try `symm`"
  symm
  -- Hint (hidden := true) "**Robo**:  Gut.  Und jetzt `apply sum_subset`."
  Hint (hidden := true) "Now try out `apply sum_subset`"
  apply sum_subset
  /-
  Hint "
    **Robo**:  Hier kannst du bestimmt `Icc_subset_Icc_iff` gut gebrauchen.
  "
  -/
  · grind
  · -- showing that x = 0 or 1 or 2:  see Luna L??
    /-
    Hint "
      **Robo**: Super!  Jetzt musst du nur noch zeigen, was du vorhin gesagt hattest:
      Der Ausdruck unter der Summe ist für die ersten drei Indizes Null."
    -/
    Hint "Show that term in sum is zero for first three indexes"
    /-
    Hint (hidden := true)"
      **Robo**: Ich schlage vor, du führst erst einmal alle Annahmen ein, bis da nur noch
      ```
         i ^ 3 - 3 * i ^ 2 + 2 * i = 0
      ```
      als Beweisziel steht.
    "
    -/
    Hint (hidden := true) "Introduce assumptions until ``` i ^ 3 - 3 * i ^ 2 + 2 * i = 0 ``` as goal"
    Branch
      simp
      intro i h0 h3
      /-
      Hint "**Robo**:  Aus den Annahmen muss ja irgendwie folgen ${i}=0$ oder ${i}=1$ oder ${i}=2$.
    Vielleicht formulierst du das mit `have` explizit aus."
    -/
      Hint "Assumptions have to entail ${i}=0$ or ${i}=1$ or ${i}=2$. Try `have`"
    intro i h0 h3
    /-
    Hint "**Robo**:  Aus den Annahmen muss ja irgendwie folgen ${i}=0$ oder ${i}=1$ oder ${i}=2$.
    Vielleicht formulierst du das mit `have` explizit aus."
    -/
    Hint "Assumptions have to entail ${i}=0$ or ${i}=1$ or ${i}=2$. Try `have`"
    have h : i = 0 ∨ i = 1 ∨ i = 2 := by
      Branch
        Hint (hidden := true) "Try `simp` & `omega`"
        simp at h0 h3
        omega
      grind
      /-
      Hint (hidden := true) "
        **Robo**:  Irgendeine Kombination von `simp` und `omega` wird das schon lösen.
        Hat doch auf Luna auch geklappt.
      "
      -/
    /-
    Hint (hidden := true) "
      **Robo**:  Die Annahme {h} kannst du ja jetzt mit `obtain h | h | h  := {h}` in die drei Fälle aufteilen.
    "
    -/
    Branch
      Hint (hidden := true) "[Babylon] Split `{h}` with `obtain`: `obtain h | h | h  := {h}`"
      obtain h | h | h  := h
      · rw [h]
        ring
      · rw [h]
        ring
      · rw [h]
        ring
    grind

/---/
TheoremDoc Finset.sum_subset as "sum_subset" in "∑ Π"
NewTheorem Finset.sum_subset

NewDefinition Finset.Icc

TheoremTab "∑ Π"
