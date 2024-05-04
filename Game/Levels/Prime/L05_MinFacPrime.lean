import Game.Metadata

World "Prime"
Level 5

Title "Unendlich viele Primzahlen"

Introduction "
**Irgendeine Person**: Ich bin auf der Suche nach der grössten Primzahl.

**Du**: Dann viel Erfolg.

**Person**: Wieso?

**Du**: Na es gibt unendlich viele!

**Person**: Wieso?

**Du**: Lass uns mal mit folgendem anfangen: Für jede Zahl exisitiert eine Primzahl, die
grösser ist.

**Person**: Welche denn?

**Du** Entweder das Produkt aller Primfaktoren von $n$ plus Eins, oder $n! + 1$.

**Robo**: Zu $n! + 1$ kann ich besser helfen, hier zum Beispiel:
"

Conclusion "**Person**: Die ist schon mal grösser als die grösste Zahl, die ich je angeschaut
habe!
"

-- Damit die Notation `n !` funktionieren.
open Nat

Statement minFac_factorial_succ_prime (n : ℕ) : Nat.Prime (minFac (n ! + 1)) := by
  Hint "Das ist mehrheitlich `minFac_prime`."
  apply minFac_prime
  by_contra h
  rw [succ_inj] at h
  have := factorial_ne_zero n
  contradiction

/---/
TheoremDoc Nat.minFac_prime as "minFac_prime" in "Prime"

/---/
TheoremDoc Nat.factorial_ne_zero as "factorial_ne_zero" in "Prime"

/---/
TheoremDoc Nat.succ_inj as "succ_inj" in "Prime"

/-- Der kleinste Primfaktor einer natürlichen Zahl. -/
DefinitionDoc Nat.minFac as "minFac"

/-- Eine Primzahl.

Achtung: Lena kennt `Nat.Prime` (eine Primzahl) sowie `Prime` (ein Primelement) -/
DefinitionDoc Nat.Prime as "Prime"

/--`factorial n` oder `n !` ist das Produkt aller natürlichen Zahlen von `1` bis `n`. -/
DefinitionDoc Nat.factorial as "(·) !"


NewTheorem Nat.minFac_prime Nat.factorial_ne_zero Nat.succ_inj
NewDefinition Nat.minFac Nat.Prime Nat.factorial
