import Game.Metadata

World "SetTheory"
Level 1

Title "Mengen"

-- macro_rules | `(tactic| trivial) => `(tactic| simp <;> trivial)
-- macro_rules | `(tactic| trivial) => `(tactic| tauto)
-- macro_rules | `(tactic| trivial) => `(tactic| fail "Some goals were not trivial!")

Introduction
"
**Mengea**: Ich würde leider den Inhalt jenes Buches eh nicht verstehen. Aber der beste Weg für
euch, dieses zu entschlüsseln ist, euch ausgiebig mit der Bevölkerung hier zu unterhalten.
Lebt mit ihnen, redet mit ihnen und ihr werdet die Sprache automatisch lernen.

**Mengea**: Seid aber vorgewarnt, die Leute hier denken ganz viel über Mengen nach,
womit sie immer *homogene Mengen* meinen. Eine Menge natürlicher Zahlen `{1, 4, 6}` ist
verständlich, aber sowas wie eine Menge `{(2 : ℕ), {3, 1}, \"e\", (1 : ℂ)}` gibt es hier
einfach nicht. Punkt.

**Robo**: Als Kontext: Wenn `A` ein beliebiger `Type` ist, dann ist `(U : Set A)` eine Menge
mit Elementen aus `A`

**Mengea**: Damit ich weiß, dass ihr euch grundsätzlich mit den Leuten austauschen könnt,
erklärt mir doch folgendes:
"

open Set

Statement Set.mem_univ {A : Type} (x : A) : x ∈ (univ : Set A) := by
  Hint "
    **Du**: Also `A` ist ein `Type`, `x` ist ein Element in `A`…

    **Robo** … und `univ` ist die Menge aller Elemente in `A`.

    **Du** ist das nicht einfach `A` selber?

    **Robo** Fast, aber das eine ist ein `Type`, das andere eine Menge, also vom Typ `Set A`.

    **Du**: Unlogisch?

    **Mengites**: Naja, Typen und Mengen sind halt zwei unterschiedliche Sachen und wenn ihr
    über Mengen sprechen wollt, müssen alles Mengen sein.

    **Du**: Na gut. Und wieso `x ∈ univ` und nicht `x : univ` wie bei Typen?

    **Robo**: Jedes Element `(x : A)` hat entweder die Eigenschaft `x ∈ U` (`\\in`) oder `x ∉ U`
    (`\\nin`) für eine Menge `(U : Set A)`.

    **Du**: Also das ist ja dann `trivial`. Hoffentlich sehen die das hier auch so…"
  simp

/--
Die Menge `(univ : Set A)` ist die Menge aller Elemente in `A`. Obwohl mathematisch `A` und
`(univ : Set A)` so erscheinen, als seien sie das gleiche, ist das in Leans Typentheorie nicht so.
Elemente haben immer Typ `x : A`, aber sie können Elemente von verschiedenen "Teilmengen" von `A`
-- `U : Set A` -- sein. Z.B. gilt immer `x ∈ univ` und nie `x ∈ ∅`.
-/
DefinitionDoc Set.univ as "univ"

/--
TODO. Siehe `univ`.

`x ∉ A` ist eine Notation für `¬ (x ∈ A)`.

(`\in`, `\nin`)
-/
DefinitionDoc Set.mem as "∈"

NewDefinition Set.univ Set.mem
TheoremTab "Set"

Conclusion "**Mengea**: Ja das stimmt schon. Dann wünsche ich euch viel Erfolg auf eurer Reise!"
