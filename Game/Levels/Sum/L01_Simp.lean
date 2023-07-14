import Game.Metadata

import Game.ToBePorted

set_option tactic.hygienic false

World "Sum"
Level 1

Title "Simp"

Introduction
"
**Babylonier**:  Jeder Turm hat eine Inschrift.  Da könnt ihr noch einmal genau nachlesen, warum er steht.  Hier zum Beispiel.  
"

-- Eine endliche Summe läuft erstmal immer über einen endlichen Index
-- `Fin n`, welcher $n$ Elemente
-- $\\{0, 1, \\ldots, n-1\\}$ beinhaltet.

-- Der Syntax für  $\\sum_{i=0}^n a_i$ ist `∑ i : Fin n, _` (\\sum)

-- Als erstes kann die Taktik `simp` (für \"simplification\") ganz viel Triviales vereinfachen.
-- `simp` ist eine der stärksten Taktiken in Lean und verwendet
-- ganz viele markierte Lemmas um das Goal zu vereinfachen.

-- Zum Beispiel kennt es ein Lemma das ungefähr so aussieht:

-- ```
-- @[simp]
-- lemma sum_const_add (n : ℕ) : (∑ i in Fin n, 0) = 0 := by
--   sorry
-- ```

-- Die Taktik `simp` benützt alle Lemmas, die mit `@[simp]` markiert sind.

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
    Wir fangen besser an, sie zu benutzen.

    Irgendwie hast du das Gefühl, ein Déjà-vue zu haben …"
  simp

OnlyTactic simp
LemmaTab "Sum"

Conclusion "**Babylonier**: Seht ihr, das passt!"

-- TODO: Cannot write $\\{0\\}$ inside a hint.
