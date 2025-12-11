import Game.Metadata
import Game.Levels.Cantor.L01_CantorPowerset

World "Cantor"
Level 2

Title "" -- "Cantor's Diagonalargument"

/-
Introduction
"
**Cantor**:  Passt auf, die Überlegung geht eigentlich noch weiter!

Er greift in seinen Zylinder, und holt alle möglichen Dinge heraus.
Eine alte Zahnbürste, ein Kartenspiel, ein weißes Kaninchen …
Schließlich kommt ein zerknüllter Zettel zum Vorschein.

**Cantor**: Hier sind ja meine Notizen!  Tada!  Mein berühmtes Diagonalargument!

Er faltet den Zettel auf, reißt vorsichtig die oberste Zeile ab,
und lässt sie zu euch hinuntersegeln.
Dann beugt er sich neugierig über den Bühnenrand, um zu sehen, was ihr macht.
"
-/
Introduction "Intro Cantor L02"

/-
Diagonalgedanke:

Wir betrachten `f : A → Set A` als `f : A → A → Prop`.
Wir betrachten Negation als Selbstabbildung `¬ : Prop → Prop`.
Die Menge `{ a | a ∈ f a }` entspricht der Abbildung `a ↦ f a a `   in `A → Prop`,
die Menge `{ a | a ∉ f a}`  entspricht der Abbildung `a ↦ ¬ (f a a)`.
Wenn `f` surjektiv ist, existiert ein Urbild `a₀` der zweiten Menge,
also `f a₀ = { a | a ∉ f a}`.
Für dieses `a₀` ist dann `f a₀ a₀`, also die Aussage `a₀ ∈ { a | a ∉ f a}` bzw.
`a₀ ∉ f a₀`, ein Fixpunkt von `¬`.
Aber `¬` hat keine Fixpunkte.
-/


open Set Function

Statement {A : Type} : ¬ ∃ f : A → Set A, Surjective f := by
  /-
  Hint "**Du**: Das habe ich schon einmal gesehen!
  Kurz:  „Die Potenzmenge ist stets mächtiger als die Menge selbst.“
  War auch ein Widerspruchsbeweis, meine ich.

  **Robo:** Ja, aber ich würde mit `push_neg` und `intro f` anfangen."
  -/
  Hint "Start here with `push_neg` and `intro f`"
  push_neg
  intro f
  by_contra hf
  /-
  Hint "**Cantor**:  Na, was meint ihr?  Gibt es vielleicht irgendeine Menge,
  die nicht von `f` getroffen wird?"
  -/
  Hint "Is there a set, which is not hit by `f`"
  /-
  Hint (hidden := true) "**Robo**:  Probier mal die Menge von gerade!
  Du könntest sie erst einmal mit `let s := \{ a | a ∉ {f} a }` einführen."
  -/
  Hint "First, introduce set `let s := \{ a | a ∉ {f} a }`"
  let s := { a | a ∉ f a }
  /-
  Hint "**Robo**:  Super!
  Jetzt kannst du z.B. einfach mit `specialize {hf} {s}` weitermachen.
  Und wenn du später `simp` anwendest,
  kannst du mit `simp [{s}]` dafür sorgen, dass `simp` durch deine Definition hindurchsieht.
  "
  -/
  Hint "Try `specialize {hf} {s}`. When you apply `simp` later, `simp [{s}]` allows `simp` to look through
  your defintions"
  specialize hf s
  /-
  Hint "Cantor hüpft von einem Bein auf das andere."
  -/
  Hint "Cantor expresses happiness"
  obtain ⟨a, ha⟩ := hf
  /-
  Hint "**Cantor**:  Ja!

  **Du**:  Robo, könnten wir jetzt nicht das Resultat von eben verwenden?

  **Robo**:  Sorry, ging alles so schnell!  Habe ich wohl vergessen, abzuspeichern."
  -/
  Hint "`COMMENT-2` Try simp [{s}]"
  by_cases h : a ∈ f a
  · suffices hn : a ∉ f a
    · contradiction
    rw [ha] at h
    simp[s] at h
    assumption
  · apply h
    rw [ha]
    simp[s]
    assumption
