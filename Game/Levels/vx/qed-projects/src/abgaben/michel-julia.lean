import data.nat.choose.basic
import data.finset.basic
import algebra.big_operators.fin
import data.real.basic


open_locale big_operators

--Zu zeigen ist, dass die Summe von k=0 bis n von dem Binomialkoeffizienten von N+k über k gleich dem
--Binomialkoeffizienten von N+1+n über n ist.

example (n N : ℕ ): (finset.range(n+1)).sum (λ (k:ℕ), ((N+k).choose k) ) = ((N+1+n).choose n) :=
begin
  --Wir zeigen die Aussage mit Hilfe einer Induktion.
  induction n with d hd,

  --Der Induktionsanfang ist schnell gemacht (1=1).
  simp,

  --Der Nachfolger von d ist d+1, damit wir diese Umwandlung im Laufe des Beweises machen können.
  have h1: d.succ = d+1,
    exact rfl,
  rw[h1],

  --Jetzt wollen wir den letzten Summanden abspalten,
  --dafür müssen wir die Summe in andere Form bringen, um ein geeignetes Lemma zu verwenden.
  rw[← fin.sum_univ_eq_sum_range],
  rw[fin.sum_univ_cast_succ],
  simp,

  --Damit wir unsere Induktionsvorraussetzung einsetzen können,
  --müssen wir diese ebenfalls auf geeignete Form bringen.
  rw[← fin.sum_univ_eq_sum_range] at hd,

  --Jetzt können wir die Induktionsvorraussetzung einsetzen:
  rw[hd],

  --Nun machen wir einige Vereinfachungsschritte bis wir dasselbe auf beiden Seiten stehen haben.
  rw[← h1],
  refine congr_arg2 has_add.add rfl _,
  simp,
  rw[h1],
  have h2: N + 1 + d = N + (d + 1),
    ring,
  rw[h2],
end

