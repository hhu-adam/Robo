import Game.Metadata

World "Sum"
Level 1

Title "Simp"

Introduction
"
**Babylonier**: Jeder Turm hat eine Inschrift. Da könnt ihr noch einmal genau nachlesen,
warum er steht. Hier zum Beispiel.
"

-- Eine endliche Summe läuft erstmal immer über einen endlichen Index
-- `Fin n`, welcher $n$ Elemente
-- $\\{0, 1, \\ldots, n-1\\}$ beinhaltet.

-- Der Syntax für $\\sum_{i=0}^n a_i$ ist `∑ i : Fin n, _` (\\sum)

-- Als erstes kann die Taktik `simp` (für \"simplification\") ganz viel Triviales vereinfachen.
-- `simp` ist eine der stärksten Taktiken in Lean und verwendet
-- ganz viele markierte Lemmas um das Goal zu vereinfachen.

-- Zum Beispiel kennt es ein Lemma das ungefähr so aussieht:

-- ```
-- @[simp]
-- lemma sum_const_add (n : ℕ) : (∑ i in Fin n, 0) = 0 := by
--   sorry
-- ```

-- Die Taktik `simp` benutzt alle Lemmas, die mit `@[simp]` markiert sind.

-- (Tipp: `simp?` zeigt an, welche Lemmas `simp` benutzen würde.)

open BigOperators

Statement (n : ℕ) : (∑ i : Fin n, (0 + 0)) = 0 := by
  Hint "
    **Du**: Oh das ist ganz schön viel neues … mal sehen …

    Das sieht aus wie $( \\sum_i 0 + 0 ) = 0$.

    **Robo**: Genau! Man schreibt `\\sum`. Und `i : Fin n` bedeutet,
    dass summiert wird über $0$, $1$, …, $n-1$.

    **Du**: Okay. Und was mach ich jetzt?

    **Robo**: `simp` ist eine starke Taktik, die viele Terme vereinfacht.
    Wir fangen besser an, sie zu benutzen."
  simp

OnlyTactic simp simp_rw
NewTactic simp_rw
TheoremTab "Sum"

-- TODO: I think it's a bug in the game that `trans _ (Fin n) _` triggers `Fin`,
-- but for now I introduce this definition here instead of `MatrixTrace`
NewDefinition Fin

Conclusion "**Babylonier**: Seht ihr, das passt!

**Robo**: Mir fällt gerade ein, du hattest ja mal gefragt bezüglich `rw` unter Quantoren.
Mit Summen ist das das gleiche: Hier musst du immer `simp_rw` verwenden, wenn du innerhalb
einer Summe was umschreiben möchtest."

-- TODO: Add a level about `simp_rw`!
