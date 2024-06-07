import Game.Metadata

World "Sum"
Level 4

Title "Arithmetische Summe"

Introduction
"
**Babylonier**: Kommt, ich zeig Euch mal einen unserer schönsten Türme!

Nach einem kurzen Spaziergang steht ihr davon.

**Robo**: Das muss der bekannte *Gaußsche Turm von Babylon* sein!
Über den hab ich schon einmal Daten verarbeitet.

**Babylonier**: Richtig. Gauß war ein Babylonier!
"

open Fin BigOperators

/-- $2 \cdot \sum_{i = 0}^n i = n \cdot (n + 1)$. -/
Statement arithmetic_sum (n : ℕ) :
    2 * (∑ i : Fin (n + 1), i) = n * (n + 1) := by
  Hint "**Du**: Klar, die werden ja nicht oben anfangen mit bauen. Sag mal,
  wie zeige ich denn die arithmetische Summe, die hier gekritzelt steht?
  Ich würde gerne Induktion über $n$ anwenden.

  **Robo**: Wenn du meinst … Auf Leansch wäre das: `induction n with d hd`!
  Der Zusatz `with d hd` ist natürlich optional.
  Du kannst damit Namen für Induktionsvariable (d) und -hypothese (h) vorgeben."
  induction n with d hd
  Hint "**Du**: Zuerst der Induktionsanfang …

  **Robo**: Diesen kannst du oft mit `simp` abkürzen!"
  simp
  Hint "**Robo**: Jetzt der Induktionsschritt.
  Bei Induktion über endlichen Summen beginnst du den Induktionsschritt
  immer mit `rw [sum_univ_castSucc]`."

  -- $$\\sum_\{i=0}^n a_i = \\sum_{i=0}^\{n-1} a_i + a_n$$"
  rw [sum_univ_castSucc]
  -- TODO: Bug. Dieser Hint wird nicht angezeigt.
  Hint "**Du**: Oh das sieht jetz aber kompliziert aus…

  **Robo**: Da musst du etwas darüber hinweg lesen. Am besten machst du kurz `simp`,
  dann sieht's schon wieder besser aus."
  simp
  Hint "**Du**: Was bedeutet eigentlich der kleine Pfeil `↑`?

  **Robo**: Das ist eine *Coersion*. Sowas wie wenn man eine natürliche Zahl als ganze Zahl betrachtet,
  also die natürliche Abbildung `ℕ ↪ ℤ` benutzt. Oder hier, wenn ein Element `x : Fin n` als
  Element `↑x : ℕ` betrachtet wird."
  Hint (hidden := true)
  "**Robo**: Um die Induktionshypothese anzuwenden, brauchst du zuerst das Lemma `mul_add`."
  rw [mul_add]
  Hint (hidden := true)
  "**Du**: Und wie wende ich jetzt die Induktionshypothese an?

  **Robo** mit `rw` wie jede andere Annahme auch."
  rw [hd]
  Hint "**Du**: Der Rest ist einfach Rechnerei.

  **Robo**: Dann wird `ring` wohl keine Probleme haben."
  -- Hint "**Robo**: Jetzt musst du noch kurz `rw [Nat.succ_eq_add_one]` anwenden.

  -- **Du**: Aber wieso?

  -- **Robo**: Naja, `ring` ist jetzt auch noch nicht so stark, und erkennt nicht dass `n.succ`
  -- und `n + 1` das gleiche sind.

  -- **Du**: Aber das könnte man doch ändern, oder?

  -- **Robo**: Vielleicht wenn wir einmal einem Techniker begegnen, der mir ein Update
  -- einspielen kann…"
  -- Branch
  --   ring
  --   Hint "**Robo**: Wie gesagt, brauch doch `rw [Nat.succ_eq_add_one]` als Fix für meine
  --   kleinen Maken."
  -- rw [Nat.succ_eq_add_one]
  ring

NewTactic induction
NewTheorem Fin.sum_univ_castSucc Nat.succ_eq_add_one mul_add add_mul Nat.zero_eq
TheoremTab "Sum"

Conclusion "Du schaust dich um und bewunderst das Tal in dem hunderte, wenn nicht tausende,
Steintürme in allen Formen und Höhen stehen."
