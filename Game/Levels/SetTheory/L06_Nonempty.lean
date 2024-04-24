import Game.Metadata
import Game.Levels.SetTheory.L05_Empty


World "SetTheory"
Level 6

Title "Nonempty"

Introduction
"
**Du**: Kann ich noch mehr üben?

**Verkäufer**: Das Gegenteil von `A = ∅` ist `A ≠ ∅`, aber in Lean wird der Ausdruck `A.Nonempty` bevorzugt.
Dieser ist dadurch existiert, dass in `A` ein Element existiert: `∃x, x ∈ A`.

Zeige dass die beiden Ausdrücke äquivalent sind:
"

open Set

Statement Set.nonempty_iff_ne_empty
    {A : Type _} (s : Set A) :
    s.Nonempty ↔ s ≠ ∅ := by
  Hint "**Robo**: Am besten fängst du mit `unfold Set.Nonempty` an."
  unfold Set.Nonempty
  Branch
    -- Hint "Mit `ne_eq` und `eq_empty_iff_forall_not_mem` kannst du hier weiterkommen."
    rw [ne_eq, eq_empty_iff_forall_not_mem]
    Hint (hidden := true) "`push_neg` kann hier helfen."
    push_neg
    rfl
  constructor
  · intro h
    Hint "**Du**: Eben hatten wir doch etwas zu `{s} = ∅`.

    **Robo**: Das war `eq_empty_iff_forall_not_mem`. Du kannst ja einen
    Widerspruchsbeweis anfangen, dann kannst du dieses Lemma an der Annahme `{s} = ∅`
    benutzen!"
    Hint (hidden := true) "**Robo** Widerspruch war `by_contra hf`."
    by_contra hf
    rw [eq_empty_iff_forall_not_mem] at hf
    Hint "**Du**: Also ich weiss, dass es ein `x` gibt in `{s}` und dass gleichzeitig alle
    `x` nicht in `{s}` sind, das ist doch ein Widerspruch!

    **Robo**: Ja aber nur `contradiction` wird noch nicht reichen, da diese noch nicht
    syntaktisch negationen voneinander sind.

    **Du**: Na dann sollte das zumindest eine Tautologie sein."
    Branch
      rcases h with ⟨x, hx⟩
      -- TODO: bad style
      apply hf
      assumption
    tauto
  · Branch
      intro h
      Hint "**Du**: Vermutlich sollten wir hier aber dafür
      einen Beweis per Widerspruch anfangen?"
      by_contra hf
      Branch
        push_neg at *
        Hint "**Robo**: Für dieses Problem ist es vermutlich besser nur
        `push_neg at {hf}` zu verwenden, damit `{h}: {s} ≠ ∅` unverändert bleibt!

        **Du**: Wieso macht `push_neg` denn das?

        **Robo**: Weiss ich auch nicht…
        "
        -- TODO: Why does `push_neg` do this with `h`?
      push_neg at hf
      Hint (hidden := true) "**Du**: Ist das nicht nochmals eine Seite des Lemmas von
      vorhin?

      **Robo**: Ja, `eq_empty_iff_forall_not_mem` ist nochmals nützlich"
      rw [← eq_empty_iff_forall_not_mem] at hf
      contradiction
    Hint "**Robo**: Mein System sagt, dass Kontraposition nützlich sein könnte.

    **Du**: Ja, dann sieht es schon wieder ähnlich dem Lemma von vorhin."
    contrapose
    Branch
      intro h
      Hint (hidden := true) "**Robo**: `push_neg at *` könnte helfen die ganzen `¬` wegzukriegen."
      push_neg at *
    Branch
      simp
    push_neg
    intro h
    Hint (hidden := true) "**Du**: Und wie hies das Lemma nochmals?

    **Robo**: `eq_empty_iff_forall_not_mem`."
    rw [eq_empty_iff_forall_not_mem]
    assumption

NewDefinition Set.Nonempty
TheoremTab "Set"
