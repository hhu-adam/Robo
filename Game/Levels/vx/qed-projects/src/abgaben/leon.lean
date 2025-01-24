import algebra.category.Group.basic
import group_theory.order_of_element
import data.fintype.card
import tactic.fin_cases
import algebra.group.defs


-- Es soll gezeigt werden, dass alle Gruppen der Ordnung kleiner gleich 3
-- abelsch sind, also für zwei beliebige Elemente a, b der Gruppe a*b = b*a gilt. 
theorem abelsche_Gruppen (G : Type) [group G] [fintype G] (a b: G) (n:ℕ) (h1: n>0) (hn: fintype.card G = n) : n < 4 → (a*b = b*a):= 
begin

-- Zuerst wird mit intro die Gruppenordnung als Annahme aufgenommen und
-- dann mit fin_cases eine Fallunterscheidung für die einzelnen Gruppenordnungen gemacht. 
intro h,
set k: fin 4:= ⟨n, h⟩,
fin_cases k,

-- Hier wird der Fall behandelt, dass die Gruppenordnung gleich 0 ist, obwohl eine Gruppe 
-- immer mindestens das neutrale Element enthalten muss, also mindestens Gruppenordnung eins hat, aber
-- Lean macht auch den Fall für 0.
{suffices h2: a = b,
  {rw [h2]},

  -- Dieser Schritt wird bei jedem der vier Fälle gemacht, damit für die 
  -- einzelnen Fälle auch die Grupenordnung mit der richtigen Zahl in den Annahmen steht.
  {have h3: n=0,
  {
    suffices j : n = k.val,
    suffices jj : k.val = 0,
    tauto,
    rcases this,
    exact j.symm,
    simp,
  },
  rw h3 at hn,
  apply fintype.card_le_one_iff.mp,
  rw hn,
  exact zero_le 1,
  },
},


-- Fall Gruppenordnung = 1: Da die Gruppe nur ein Element hat muss
-- für zwei Elemente a,b aus G a = b gelten und damit a*b = b*a.
{suffices h2: a = b,
  {rw [h2]},
  {have h3: n=1,
  {
    suffices j : n = k.val,
    suffices jj : k.val = 1,
    tauto,
    rcases this,
    exact j.symm,
    simp,
  },
  rw h3 at hn,
  apply fintype.card_le_one_iff.mp,
  exact (eq.symm hn).ge,
  },
},


-- Fall Gruppenordnung = 2:
{suffices h2: a = 1 ∨ a = b ∨ b = 1,
  {rcases h2 with ha|hb|hc,
  rw ha,
  rw mul_one,
  rw one_mul,
  rw hb,
  rw hc,
  rw one_mul,
  rw mul_one,
  },
{have h3: n=2,
  {
    suffices j : n = k.val,
    suffices jj : k.val = 2,
    tauto,
    rcases this,
    exact j.symm,
    simp,
  },
  {by_cases h5: b = 1,
  tauto,
  rw ←or_assoc,
  left,
  by_cases h6: a = 1,
  tauto,
  right,
  rw h3 at hn,
  -- Rest des Beweises (habe es aber nicht geschafft in Lean umzusetzen): Wir wissen, dass die Gruppe zwei Elemente
  -- hat. Eines davon ist das neutrale Element eins. Außerdem wissen wir durch die 
  -- Annahmen h5 und h6, dass weder a noch b gleich eins sind. Da es aber nur ein anderes 
  -- Element außer der eins in der Gruppe gibt, folgt a = b.
  sorry,
  },
},
},


-- Fall Grupenordnung = 3:
{suffices h2:  a = 1 ∨ a = b ∨ b = a⁻¹ ∨ b = 1,
  {rcases h2 with ha|hb|hc|hd,
  rw ha,
  rw mul_one,
  rw one_mul,
  rw hb,
  rw hc, 
  rw mul_right_inv,
  rw mul_left_inv,
  rw hd,
  rw mul_one,
  rw one_mul,
  },
{have h3: n=3,
  {
    suffices j : n = k.val,
    suffices jj : k.val = 3,
    tauto,
    rcases this,
    exact j.symm,
    simp,
  },
  {by_cases h5:  b = 1,
  tauto,
  by_cases h6: a = 1,
  tauto,
  by_cases h7: a = b,
  tauto,
  rw h3 at hn,
  right,
  right,
  left,
  sorry,
  -- Beweisidee für das sorry:
  -- Da die Gruppenordnung 3 ist und die Ordnung jedes Elementes von G
  -- ein Teiler von der Gruppenordnung ist, so folgt, dass die Ordnung des Elements
  -- a gleich 1 oder gleich 3 sein muss. 
  -- nicht erfolgreicher Versuch dies in Lean umzusetzen:
  -- {have h8: order_of a = 1 or order_of a = 3,
  -- {apply order_of_dvd_card_univ}}
  -- Da nach der Annahme h6 a ungleich eins ist, so muss die Ordnung von a gleich 3 sein.
  -- Dadurch wissen wir, dass a ungleich a^-1 ist, da sonst die Ordnung von a gleich 2 wäre.
  -- Also folgt b = a^-1, da a ungleich 1 und a ungleich a^-1, so muss das dritte Element der Gruppe das Inverse
  -- zu a sein und das ist b, da durch Annahme h7 a ungleich b.
  },
},
},
end




