import data.nat.prime
import data.set.finite
import tactic.linarith
import algebra.big_operators.order

-- Damit die Notationen `∏` und `n!` funktionieren.
open_locale big_operators nat

open nat

theorem unenlich_viele_primzahlen :
  ∀ n, ∃ p, nat.prime p ∧ n < p :=
begin
  intro n,

  -- Wir nehmen an, dass `n` eine beliebige natürliche Zahl ist.

  -- Wir wählen einen beliebigen Primfaktor `q` von `n! + 1` und zeige, dass er größer als `n` ist.
  let q := min_fac (n! + 1),
  -- Die Funktion `min_fac` gibt den kleinsten Primfaktor einer Zahl zurück.
  -- Hier wählen wir den kleinsten Primfaktor von `n! + 1` und bezeichnen ihn als `q`.
  use q,

  -- Wir wollen zeigen, dass `q` eine Primzahl ist und größer als `n`.

  -- Wir zeigen, dass `q` eine Primzahl ist.
  have q_prime : nat.prime q := min_fac_prime _,
  -- Die Funktion `min_fac_prime` besagt, dass der Rückgabewert von `min_fac` wieder eine Primzahl ist.

  -- Nun müssen wir erstmal nur noch zeigen, dass `q` größer als `n` ist:

  -- Dazu gehen wir wie folgt vor und machen folgende Annahme: Angenommen, `q` ist kleiner oder gleich `n`.
  by_contradiction h,
  -- Wir machen einen Widerspruchsbeweis und nehmen an, dass `q` kleiner oder gleich `n` ist.

  -- Da `q` ein Primfaktor von `n! + 1` ist und größer als `n`, kann `q` ja gar  kein Teiler von `n!` sein. Das wollen wir zum Widerspruch führen.
  have hq : q ∣ n! + 1 := min_fac_dvd _,
  -- Die Funktion `min_fac_dvd` besagt, dass der Rückgabewert von `min_fac` der kleinste Teiler der gegebenen Zahl, hier q, ist.

  have hq₁ : q ∣ n! := dvd_of_dvd_add_left hq,
  -- Da `q` ein Teiler von `n! + 1` ist, ist `q` auch ein Teiler von `n!`. (Stimmt natürlich nicht, wollen wir zum Widerspruch führen)

  have hq₂ : q ∣ 1 := dvd_add_iff_right.mp hq₁,
  -- Da `q` ein Teiler von `n!` ist und `q` ein Teiler von `n! + 1` ist, muss `q` auch ein Teiler von `1` sein.

  -- Da `q` eine Primzahl ist, kann sie `1` sein und somit auch kein Teiler von `1` sein, da der einzige Teiler der 1, die 1 selber ist.
  exact absurd hq₂ not_dvd_one q_prime,
  -- Daher muss unsere Annahme falsch sein.
  -- Dies zeigt, dass es immer eine Primzahl `p` gibt, die größer als `n` sein muss.

end



