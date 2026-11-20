import Game.Metadata
import Game.Levels.Cantor.L09_CantorDiag

World "Cantor"
Level 10

Title ""

open Function Set

/---/
TheoremDoc surjective_mem_of_surjective as "surjective_mem_of_surjective" in "Function"

/-
Introduction "
**Cantor**: Und jetzt nehmt ihr dieses schöne Diagonalargument und zeigt noch einmal,
dass es keine surjektiven Abbildungen `A → Set A` gibt!
Ihr müsst nur `Set A` auffassen als `A → Prop`!

**Du**: Was?

**Robo**:  Eine Teilmenge `S : Set A` kann man mit der Abbildung
`A → Prop` identifizieren, die `a : A` auf die Aussage `a ∈ S` wirft.
Für Formalosophen ist das dasselbe.

**Cantor**:  Exaktemente!  Hier, ich gebe euch noch einen Zwischenschritt.
"
-/
Introduction "Intro Cantor L10: Use the diagonal argument to show once more that there are no
surjective mappings `A → Set A`, by interpreting `Set A` as `A → Prop`: a subset `S : Set A`
can be identified with the map A → Prop sending `a : A` to `a ∈ S`. Here is an intermediate step."

Statement surjective_mem_of_surjective {A : Type} (f : A → Set A) (hf : Surjective f) :
    Surjective (fun a ↦ (fun x ↦ x ∈ f a)) := by
  /-
  Hint "
    **Du**:  Surjektiv heißt, jede Abbildung `p : A → Prop` hat ein Urbild.
    Also fange ich mal mit `intro` an.
  "
  -/
  Hint (hidden := true) "[Hint ragzs] Surjective means: every map `p : A → Prop` has a preimage.
  Start with `intro`."
  intro p
  /-
  **Robo**:  Die Surjektivität von `{f}` liefert dir Urbilder von *Teilmengen* von `{A}`.
  Vielleicht sollten wir mit `let` der Teilmenge, die `{p}` entspricht, einen Namen geben?
  -/
  Hint "[Hint mc68k] The surjectivity of `{f}` gives preimages of *subsets* of
  `{A}`. Introduce a name for the subset corresponding to `{p}` with `let`."
  /-
  **Robo**: Das wird wohl die Menge `\{x | {p} x }` sein, oder?
  -/
  Hint (hidden := true) "[Hint jx4gv] Consider the set `\{ x | {p} x }`."
  Branch
    specialize hf { x | p x }
    obtain ⟨a, ha⟩ := hf
    use a
    /-
    **Robo**:  Irgendeine Kombination von `simp` und `{ha}` sollte das jetzt zu Ende bringen.
    -/
    Hint (hidden := true) "[Hint mr4el] Use `simp` in combination with `{ha}`."
    simp [ha]
  let S := { x | p x }
  specialize hf S
  obtain ⟨a, ha⟩ := hf
  use a
  /-
  **Robo**:  Irgendeine Kombination von `simp`, `{S}` und `{ha}` sollte das jetzt zu Ende bringen.
  -/
  Hint (hidden := true) "[Hint kq7tw] Use `simp` in combination with `{S}` and `{ha}`."
  simp [ha, S]

TheoremTab "Function"

/-
**Robo**:  Das brauchen wir bestimmt gleich.  Ich speicher das mal als `surjective_mem_of_surjective`.
-/
Conclusion "Conclusion Cantor L10: We will surely need this in a moment. I'll save it as
`surjective_mem_of_surjective`."
