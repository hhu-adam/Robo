import Game.Levels.Mono.L03_NotInjective

World "Mono"
Level 4

Title "" -- ""

Introduction ""

open Function Nat

-- How we write the definition of `diag` – whether as `(fun a _ ↦ a)` or `fun a ↦ (fun i ↦ a)`  or `…`
-- does not affect the way it is displayed in the game!
Statement {A : Type} (n : ℕ) :
    let diag : A → Fin (n + 1) → A := fun a i ↦ a
    Injective (diag) := by
  /-
  Hint "**Du**:  In der Definition von `diag` stehen wieder zwei Pfeile hintereinander.
  Das muss ich erst mal im Kopf sortieren.

  **Robo**:  Setz als erstes wieder Klammern:  `A → (Fin (n + 1) → A)`. Es ist also
  `diag` eine Abbildung von `A` in die Menge `Fin (n + 1) → A`.
  Nun ist `Fin (n+1)` die Menge $\\\{0,1,…,n\\}$, und `Fin (n + 1) → A` demnach die Menge der Abbildung von $\\\{0,1,…,n\\}$ nach $A$.

  **Du**:  Mmh…  So eine Abbildung ist eigentlich nichts weiter als ein $(n+1)$-Tupel von Elementen aus $A$, oder?

  **Robo**: Kann man so sehen.

  **Du**:  Okay.  Gegeben ist also eine Abbildung `diag` von $A$ nach $A^\{n+1}$.  Und zwar die Abbildung …  ah, ich sehe, warum sie `diag` heißt.
  "
  -/
  Hint "Explain `diag`: in the definition add brackets so it's `A → (Fin (n + 1) → A)`. So, `diag`
  is a mapping from `A` to `Fin (n + 1) → A`. `Fin (n+1)` is the set $\\\{0,1,…,n\\}$ and therfore,
  `Fin (n + 1) → A` is the set of mappings from $\\\{0,1,…,n\\}$ to $A$. Hence, such a mapping can be seen
  as a $(n+1)$-tuple of elements in $A$. So, `diag` is given as a mapping from $A$ to $A^\{n+1}$.
  Name `diag` should be clear now"
  /-
  Hint (hidden := true) "**Du**:  Oder vielleicht doch nicht.  Kannst du das bitte nochmal aufdröseln?

  **Robo**:  Die Abbildung `diag` schickt ein Element $a$ auf die Abbildung, die *jeden* Index $i \\in \\\{0,1,…,n\\}$ auf $a$ abbildet.
  In deiner Interpretation ist das die Abbildung $a ↦ (a,…,a)$.
  "
  -/
  Hint (hidden := true) "To be more precise: `diag` sends an $a$ onto the mapping, which maps each index $i \\in \\\{0,1,…,n\\}$ onto $a$.
  In the former intepretation this is the mapping $a ↦ (a,…,a)$."
  -- Hint (hidden := true) "**Robo**: Wenn du gar nicht weiter weißt, fang am besten mal mit `unfold Injective` an."
  Hint (hidden := true) "If unsure start with `unfold Injective`"
  --unfold Injective
  Branch
    simp [diag]
    intro a b h
    -- Hint (hidden := true) "**Robo**:  Du könntest die Abbildungen in `{h}` auf einem Element aus `Fin (n + 1)` auswerten. Vielleicht hilft `congr_fun` in irgendeiner Form?"
    Hint (hidden := true) "Evaluate mappings in `{h}` on element from `Fin (n + 1)`. `congr_fun` could help"
    apply congr_fun at h
  --Branch
  --  apply HasLeftInverse.injective  -- not yet known!
  --  let p : (Fin (n + 1) → A) → A := fun v ↦ v (Fin.last n)
  --  use p
  --  tauto
  intro a₁ a₂ h
  /-
  Hint (hidden := true) "**Robo**:  Erinner dich, dass deine “Tupel” `diag {a₁}` und `diag {a₂}` in Wahrheit zwei Abbildung `Fin (n + 1) → A` sind.
  Du könntest sie auf einem Element aus `Fin (n + 1)` auswerten. Vielleicht hilft `congr_fun` in irgendeiner Form?"
  -/
  Branch
    -- old proof.
    Hint (hidden := true) "Remind that 'tuples' `diag {a₁}` and `diag {a₂}` are two mappings `Fin (n + 1) → A`.
    Evaluate them on elements from `Fin (n + 1)`. Try `congr_fun`"
    apply congr_fun h 0
  grind
