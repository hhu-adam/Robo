-- Level name : Automatisierung

import data.nat.basic
import data.nat.order.basic
import tactic.ring

/-
Solche Rechnungen können von Hand ziemlich anstrengend sein.

Die Taktik `ring` kann Gleichungen über jedem kommutativen Ring lösen.
-/

/- Lemma : no-side-bar
Einzeiler.
-/
example (a b c : ℕ) : (a * a + a * b + a * b + b * b) * c = (a + b) * (b + a) * c :=
begin
  ring,
end

/- Tactic : ring
Löst Gleichungen in einem kommutativen Ring.
-/
