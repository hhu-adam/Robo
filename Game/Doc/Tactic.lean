import GameServer.Commands

/--
Mit `apply` wendest du eine Implikation `hAB : A → B` an:

| vorher | Taktik           | nachher |
|:------------ |:---------------- |:-------- |
| `⊢ B`        | `apply hAB`      | `⊢ A`    |
| `h : A `     | `apply hAB at h` | `h : B`  |

In beiden Fällen kann die Implikation `hAB` wahlweise
als Annahme gegeben oder ein bereits bekanntes Lemma sein.
-/
TacticDoc apply

/--
Die Taktik `assumption` schließt den Beweis, wenn eine der Annahmen genau dem Beweisziel entspricht.
-/
TacticDoc assumption

/--
Die Taktik `by_cases h : P` beginnt eine Fallunterscheidung, ob `P` wahr oder falsch ist.
Zum Beispiel unterscheidet `by cases h : a = b` die Fälle `a = b` und `a ≠ b`.

Das Beweisziel wird hierzu dupliziert, und
in der ersten „Kopie“ wird die Annahme `(h : P)` hinzugefügt,
in der zweiten „Kopie“ die Annahme `(h : ¬P)`.
-/
TacticDoc by_cases

/--
Die Taktik `by_contra h` leitet einen Widerspruchsbeweis ein.
Ist `P` dein aktuelles Beweisziel, so generiert `by_contra h` eine neue Annahme `(h : ¬ P)`
und setzt das Beweisziel auf `False`.

## Freunde und Verwandte

* Am Ende eines Widerspruchsbweises braucht man gewöhnlich `contradiction`:
diese Taktik schließt den Besweis, wenn sie zwei offensichtlich widersprüchlichen Annahmen.
* Ist das Beweisziel von der Form `A → B`, kannst du mit `contrapose`
einen Beweis durch Kontraposition führen.
-/
TacticDoc by_contra


/-
`change t` ändert das Beweisziel zu `t`. Voraussetzung ist, dass `t` und das alte Beweisziel
definitionsgleich sind.
Dies ist insbesonder hilfreich, wenn eine Taktik nicht merkt,
dass das Beweisziel definitionsgleich  ist zu einem
Term, der eigentlich gebraucht würde.

## Beispiel

Aktuelle Beweislage:
```
b: ℝ
⊢ 1 • b = b
```
wobei die Skalarmultiplikation als `fun (a : ℚ) (r : ℝ) => ↑a * r` definiert war.
Hier kannst du mit `change (1 : ℚ) * b = b` das Beweisziel umschreiben und anschliessend mit Lemmas
über die Multiplikation beweisen.
-
TacticDoc change
-/

/--
Eine Annahme der Form
```
h : ∃ (b : B), P b
```
kannst du mit
`choose b hb using h` in die Bestandteile `b : A` und `hb : P b`
zerlegen.

Allgemeiner kannst du `choose` verwenden, um Elemente mit dem Auswahlaxiom zu wählen:
aus einer Annahme der Form
```
h : ∀ (a : A), ∃ (b : B), P a b
```
extrahiert `choose f hf using h`
eine Abbildung `f : A → B` und die Annahme `hf : ∀ (a : A), P a (f a)`.

(Hier ist `P : A → (B → Prop)` ein Prädikat, das von zwei Variablen `a` und `b` abhängt.)
-/
TacticDoc choose


/--
Die Taktik `constructor` teilt ein Beweisziel in seine Bestandteile auf:

| vorher | nachher                |
|:------------ |:----------------------- |
| `⊢ A ∧ B`    | `⊢ A` und `⊢ B`         |
| `⊢ A ↔ B`    | `⊢ A → B` und `⊢ B → A` |

## Freunde und Verwandte

* Eine *Annahme* zerlegst du mit `obtain` in ihre Bestandteile.
* Möchtest du `A ∨ B` beweisen, musst du dich mit `left` bzw. `right` für eine Seite entscheiden.
-/
TacticDoc constructor

/--
Die Taktik `contradiction` schließt den Beweis, wenn sie einen Widerspruch in den Annahmen findet.
Ein solcher Widerspruch kann zum Beispiel folgendermaßen aussehen:

* `h : n ≠ n`
* `h : A` und `h' : ¬A`
* `h : False`

## Freunde und Verwandte

Normalerweise wird `contradiction` benutzt, um einen Widerspruchsbeweis zu
schließen, der mit `by_contra` eröffnet wurde.
-/
TacticDoc contradiction

/--
Die Taktik `contrapose` ändert ein Beweisziel der Form `A → B` zu `¬B → ¬A` und leitet somit
einen Beweis durch Kontraposition ein.

## Freunde und Verwandte

Die Taktik `revert h` kann nützlich sein, um eine Annahme als Implikationsprämisse zu schreiben,
 bevor du `contrapose` verwendest.
-/
TacticDoc contrapose

/-
Die Taktik `exact h` schliesst das Beweisziel wenn der Term `h` mit dem Beweisziel übereinstimmt.
-
TacticDoc exact
-/

/--
Zwei Teilmengen einer gegebenen Menge sind gleich, wenn sie dieselben Elemente besitzen.
Steht im Beweisziel
```
A = B
```
für zwei Teilmengen von `T` (also für `A B : Set T`),
so überführt `ext x` das Beweisziel in die Äquivalenz
```
x ∈ A ↔ x ∈ B
```
-/
TacticDoc ext

/-
`fin_cases i` führt eine Fallunterscheidung, wenn `i` ein endlicher Typ ist.

## Details
`fin_cases i` ist insbesondere nützlich für `(i : Fin n)`, zum Beispiel als Index in
endlich dimensionalen Vektorräumen.

In diesem Fall bewirkt `fin_cases i` dass man Komponentenweise arbeitet.
-
TacticDoc fin_cases
-/

/--
Zwei Abbildungen mit demselben Werte- und Definitionsbereich sind gleich,
wenn sie auf allen Elementen des Definitionsbereichs dieselben Werte annehmen.
Ein Beweisziel der Form
```
f = g
```
für Abbildungen `f g : X → Y` wird durch `funext x`
in die Gleichung
```
f x = g x
```
überführt.
-/
TacticDoc funext

/--
Mit `generalize` kannst du ein Beweisziel verallgemeinern
– in der Hoffnung, dass ein höherer Abstraktionsgrad einen einfacheren Beweis erlaubt.
Genauer ersetzt `generalize h : a = b` alle Vorkommen von `a` im Beweisziel durch `b`
(und ergänzt die Annahme `h : a = b`).

## Beispiel

Ein Ziel der Form
```
Even x ∨ ¬Even x
```
lässt sich mit
```
generalize h : (Even x) = A
```
in
```
A ∨ ¬A
```
überführen (und dann einfach mit `tauto` beweisen).
-/
TacticDoc generalize

/--
Mit `have h : P` führst du ein Zwischenresultat ein.
Anschließend musst du zuerst dieses Zwischenresultat beweisen,
bevor du den eigentlich Beweis fortsetzen kannst.

## Freunde und Verwandte
`suffices h : P` funktioniert genauso, außer dass du zunächst den Hauptweise forsetzen kannst und
erst ganz am Ende dein Zwischenresultat beweisen musst.
-/
TacticDoc «have»
/-
 `let h : Prop := A ∧ B` ist verwandt mit `have`, mit dem Unterschied, dass man mit `let`
  eine temporäre Definition einführt.
-/

/--
Mit `if … then … else` kannst du Abbildungen mit zwei Definitionszweigen definieren.

Zum Beispiel definiert `fun x ↦ if 0 ≤ x then -x else x` die Betragsfunktion.
-/
TacticDoc «if»

/--
Die Taktik `induction n` führt einen Induktionsbeweis über `n`.
Mit `induction n with d dh` kannst du Namen für die Induktionsvariable (hier: `d`)
und die Induktionsannahme (hier: `hd`) vorgeben.
Die Taktik ersetzt also das ursprüngliche Beweisziel durch zwei neue Beweisziele:
* einen Induktionsanfang, in dem `n = 0` gesetzt wird, und
* einen Induktionsschritt, in dem dir die Induktionsannahme `hd` zur Verfügung steht.

## Modifikationen in diesem Spiel

Außerhalb dieses Spiels heißt `induction` `induction'`,
`0` wird zunächst als `Nat.zero` and `d + 1` als `Nat.succ d` geschrieben.
Diese Terme sind jeweils definitionsgleich, müssen aber gelegentlich mit
`zero_eq` und `Nat.succ_eq_add_one` explizit umgeschrieben werden.
-/
TacticDoc induction
/- richtige `induction`-Syntax:
```
induction n with
| zero =>
  sorry
| succ m m_ih =>
  sorry
```
Da diese sich über mehrere Zeilen erstreckt, wird sie im Spiel nicht eingeführt.

Hifreiche Resultate

* `Nat.succ_eq_add_one`: schreibt `n.succ = n + 1` um.
* `Nat.zero_eq`: schreibt `Nat.zero = 0` um.

Beide sind definitionsgleich, aber manche Taktiken können nicht damit umgehen

* `obtain ⟨⟩ := n` ist sehr ähnlich zu `induction n`. Der Unterschied ist, dass bei
`obtain` keine Induktionshypothese im Fall `n + 1` zur Verfügung steht.
-/


/--
Die Taktik `intro` wird für Beweisziele Form `A → B` oder `∀ x, P x` verwendet.

Ist dein Beweisziel `A → B`, erhältst du mit `intro h` die Annahme `h : A`, und musst dann
`B` beweisen.
Ist dein Beweisziel `∀ x, P x`, gibst du dir mit `intro x` ein beliebiges `x` vor und musst dann `P x` beweisen.

| vorher | Taktik       | nachher                     |
|:------------ |:------------ |:---------------------------- |
| `⊢ A → B`    | `intro h`    | `h : A`, `⊢ B`               |
| `⊢  x, P x`  | `intro x hx` | `x : X`, `hx : P x`, `⊢ P x` |


## Freunde und Verwandte

Die Taktik `revert h` macht das genaue Gegenteil von `intro h`.
-/
TacticDoc intro

/--
Wenn das Beweisziel von der Form `A ∨ B` ist, enscheidest du dich mit `left`, die linke Seite zu zeigen.

## Freunde und Verwandte

Mit `right` entscheidest du dich entsprechend für die rechte Seite.
-/
TacticDoc left

/-- Die Taktik `let` führt eine temporäre Definition ein, zum Beispiel
`let x : ℕ := 5 ^ 2`.
-/
TacticDoc «let»
-- * `have x : ℕ := 5 ^ 2` führt ebenfalls eine neue natürliche Zahle `x` ein, aber
--  Lean vergisst sofort, wie die Zahl definiert war. D.h. `x = 25` wäre dann nicht
--  beweisbar. Mit `let x : ℕ := 5 ^ 2` ist `x = 25` durch `rfl` beweisbar.
--
-- * `set x : ℕ := 5 ^ 2` macht das Gleiche wie `let` aber versucht auch `x` im Beweisziel überall einzusetzen wo `5 ^ 2` steht.
-- we decided not to introduce `set`

/-
`set f := _` funktioniert wie `let` aber versucht auch `f` im Beweisziel überall einzusetzen.
-
TacticDoc set
-/

/--
Die Taktik `linarith` kann zeigen, dass eine lineare Gleichung oder Ungleichung aus gegebenen Gleichungen oder Ungleichungen folgt.
Sie ist recht flexibel, und funktioniert genauso gut in ℕ wie in ℝ.
Die (Un)Gleichungen müssen aber gut lesbar gegeben sein. Eine Annahme der Form
```
h : m ≤ x → n < x
```
muss beispielsweise erst mit
```
rw [imp_iff_or_not] at h
```
zu
```
h : n < x ∨ ¬m ≤ x
```
umgeschrieben werden, damit `linarith` damit etwas anfangen kann.
-/
TacticDoc linarith

/--
Die Taktik `omega` kann zeigen, dass eine lineare Gleichung oder Ungleichung in `ℕ` oder `ℤ`
aus gegebenen Gleichungen oder Ungleichungen folgt.
Sie ist weniger wählerisch als `linarith`, was die Präsentation dieser (Un)Gleichungen anbelangt.
-/
TacticDoc omega

/--
Die Taktik `push_neg` schiebt Negation an Quantoren vorbei:

| vorher       | nachher      |
|:------------ |:-------------|
| `¬∀ x, P x`  | `∃ x, ¬P x`  |
| `¬∃ x, P x`  | `∀ x, ¬P x`  |

Bei geschachtelten Ausdrücken schiebt sie die Negation `¬` soweit nach rechts wie möglich.
Zum Beispiel wird aus dem Beweisziel
```
  ¬ ∀ ε, ∃ δ, ∀ y, | x - y | < δ → | f x - f y | < ε
```
mit `push_neg`
```
  ∃ ε, ∀ δ, ∃ y, ¬ (| x - y | < δ → | f x - f y | < ε)
```

## Freunde und Verwandte

Die beiden Lemmas `not_forall` und `not_exists` können mit `rw` einzeln angewendet werden.
-/
TacticDoc push_neg

/--
Die Taktik `obtain` teilt eine Annahme in ihre Einzelteile auf.

| vorher       | Taktik                 | nachher                                   |
|:------------------ |:---------------------- |:------------------------------------------ |
| `h : A ∧ B`        | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A` und `h₂ : B`                      |
| `h : A ↔ B`        | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A → B` und `h₂ : B → A`              |
| `h : Nonempty X`   | `obtain ⟨x⟩ := h`      | `x : X`                                    |
| `h : ∃ x : X, P x` | `obtain ⟨x, hx⟩ := h`  | `x : X` und `hx : P x`                     |
| `h : A ∨ B`        | `obtain h \| h := h`   | ein Ziel mit `h : A`, ein Ziel mit `h : B` |

Die Klammern in den ersten vier Beispielen tippst du als `\<` bzw. `\>`.
Hier ist `⟨_, _⟩` der *anonyme Konstruktor*.
Du kannst ihn dir ungefähr so vorstellen wie die Tupel-Notation in
„eine abelsche Gruppe ist ein Tupel $(G, 0, +)$ derart, dass …“.
-/
TacticDoc obtain
--
-- * Die Wildcard `obtain ⟨⟩ := h` entscheidet selbständig, welcher Fall vorliegt und
--   benennt die entehenden Annahmen.
--
-- * Für `n : ℕ` hat `obtain ⟨⟩ := n` einen ähnlichen Effekt wie `induction n` mit dem Unterschied,
--   dass im Fall `n + 1` keine Induktionshypothese zur Verfügung steht.

/-
`refine' { .. }` wird benötigt um eine Struktur (z.B. ein $R$-Modul) im Taktikmodus in einzelne
Beweisziels aufzuteilen. Danach hat man ein Beweisziel pro Strukturfeld.

(*Bemerkung*: Es gibt in Lean verschiedenste bessere Varianten dies zu erreichen,
z.B. \"Term Modus\" oder \"anonyme Konstruktoren\", aber für den Zweck des Spieles bleiben wir
bei diesem Syntax.)
-
TacticDoc refine'
-/

/--
Die Taktik `revert h` fügt die Annahme `h` als Implikationsprämisse ins Beweisziel ein:
aus `h : A` und `⊢ B` wird `⊢ A → B`.

## Freunde und Verwandte

Die Taktik `intro h` macht das genaue Gegenteil von `revert h`.
-/
TacticDoc revert


/--
Die Taktik `rfl` beweist `X = X`.  Genauer schließt `rfl` jedes Beweisziel der Form `A = B`,
in dem `A` und `B` definitionsgleich sind.
-/
TacticDoc rfl
-- rfl beweist auch 1 + 1 = 2 in ℕ, denn intern sind beide Seiten `0.succ.succ`.

/--
Wenn das Beweisziel von der Form `A ∨ B` ist, enscheidest du dich mit `right`, die rechte Seite zu zeigen.

## Freunde und Verwandte

Mit `left` entscheidest du dich entsprechend für die linke Seite.
-/
TacticDoc right

/--
Die Taktik `ring` beweist Gleichungen mit den Operationen `+, -, *, ^` in Halbringen,
also insbesondere in ℕ, ℤ, ℚ, ℝ, …   Sie funktioniert besonders gut in kommutativen Ringen.
-/
TacticDoc ring
-- `ring` braucht Typen `R` mit Instanzen `Ring R` oder `Semiring R`.
-- Die Taktik ist besonders auf kommutative Ringe (`CommRing R`) ausgelegt.

/--
Hast du eine Gleichung `h : X = Y` oder eine Äquivalenz `h : X ↔ Y` als Annahme oder als Lemma gegeben,
so kannst du mit `rw [h]` alle Vorkommen von `X` im Beweisziel durch `Y` ersetzen.

## Varianten

* `rw [←h]` wendet `h` rückwärts an, ersetzt also alle `Y` durch `X`.
* `rw [h, g, ←f]` wendet `h`, `g` und (rückwärts) `f` an.
* `rw [h] at h₂` führt die Ersetzungen in der Annahme `h₂` durch, nicht im Beweisziel
* `nth_rw`: Besitzt `h` Argumente, z.B. `n` in
   ```
   h : ∀ n, 2*n = f n
   ```
   oder in
   ```
   h (n : ℕ) : 2*n = f n
   ```
   so sucht `rw [h]` im Beweisziel von links nach rechts nach einem passenden Ausdruck,
   und ersetzt dann *alle* Vorkommen *des ersten* Ausdrucks, den die Taktik findet.
   Mit `nth_rw k [h]` kannst du stattdessen alle Vorkommen des `k`-ten Ausdrucks ersetzen.

  | vorher    | Taktik       | nachher        |
  |:----------------- |:-------------- |:----------------- |
  | `2*a + 2*b > 2*a` | `rw [h]`       | `f a + 2*b > f a` |
  |                   | `nth_rw 2 [h]` | `2*a + f b > 2*a` |
-/
TacticDoc rw

/--
Die Taktik `simp` versucht eine große Zahl an Lemmas anzuwenden, um einen gegebenen Ausdruck zu vereinfachen.
(Technisch handelt es sich um alle Lemmas in `mathlib`, die durch `@[simp]` gekennzeichnet sind.)

## Varianten

* `simp [h]` benutzt zum Vereinfachen zusätzlich die Voraussetzung `h` oder das Lemma `h`
* `simp [F]` benutzt zusätzliche die Definition von `F`
* `simp only [h,f,g]` benutzt ausschließlich die Voraussetzungen/Lemmas/Definitionen `h`, `f` und `g`
* `simp?` zeigt dir an, welche Lemmas verwendet wurden
-/
TacticDoc simp

/-
`simp_rw [h₁, h₂, h₃]` versucht wie `rw` jedes Lemma der Reihe nach zu Umschreiben zu verwenden,
verwendet aber jedes Lemma so oft es kann.

## Details

Es bestehen aber drei grosse Unterschiede zu `rw`:

* `simp_rw` wendet jedes Lemma so oft an wie es nur kann.
* `simp_rw` kann besser unter Quantifiern umschreiben als `rw`.
* `simp_rw` führt nach jedem Schritt ein `simp only []` aus und vereinfacht dadurch grundlegenste
  Sachen.
-
TacticDoc simp_rw
-/

/-- `specialize h a₁ a₂` ist äquivalent zu `have h := h a₁ a₂`: die Taktik ersetzt eine Annahme
`h : ∀ m₁ m₂, P m₁ m₂` durch den Spezialfall `h : P a₁ a₂`.

Falls du mehrmals spezialisieren möchtest, solltest du statt `specialize`
`have` verwenden, da `specialize h …` die alte Annahme `h` überschreibt.
Aus obiger Annahme `h` erhält man beispielsweise mit
```
have ha := h a₁ a₂
have hb := h b₁ b₂
```
die folgenden drei Annahmen:
```
h : ∀ m₁ m₂, P m₁ m₂
ha : P a₁ a₂
hb : P b₁ b₂
```
-/
TacticDoc specialize


/--
Mit `suffices h : P` leitest du einen Beweisabschnitt ein, in dem du zeigst,
dass das gewünschte Beweisziel aus `P` folgt.
Danach beweist du `P`.

## Freunde und Verwandte
`have h : P` funktioniert genauso, außer dass du zunächst `P` beweisen musst und erst dann
den Hauptbeweis fortsetzen kannst.
-/
TacticDoc «suffices»


/--
Mit `symm` (für „symmetry“) vertauschst du die Seiten einer Gleichung (`=`) oder Äquivalenz (`↔`) im Beweisziel.

## Varianten
* `symm at h` operiert auf der Annahme `h` statt auf dem Beweisziel
* `h.symm` ist das Ergebnis von `symm at h`, und kann wie `h` verwendet werden

Jede der drei folgenden Taktiken bzw. Taktiksequenzen hat also denselben Effekt:
* `rw [←h]`
* ```
  symm at h
  rw [h]
  ```
* `rw [h.symm]`
-/
TacticDoc symm

/--
Mit `trans` fügst du in eine Gleichung oder Äquivalenz einen Zwischenschritt ein.

| vorher | Taktik    | nachher                |
|:------------ |:--------- |:----------------------- |
| `⊢ A = C`    | `trans B` | `⊢ A = B` und `⊢ B = C` |
| `⊢ A ↔ C`    | `trans B` | `⊢ A ↔ B` und `⊢ B ↔ C` |

Da du die Taktik mehrmals wiederholen kannst, ist sie geeignet,
um Schritt für Schritt eine „Rechnung“ `A = B₁ = B₂ = B₃ … = C` durchzuführen.

(Außerhalb vom Spiel ist allerdings die mehrzeilige Taktik `calc` besser für derartige Rechnungen geeignet.)
-/
TacticDoc trans

/--
Mit `decide` kannst du Aussagen beweisen, die mit einem einfachen Algorithmus
entschiedbar sind.  Dazu gehören insbesondere `True` und Aussagen über konkrete Zahlen wie:
- `Even 4`
- `2 ≤ 5`
- `4 ≠ 6`
- `Prime 7`
-/
TacticDoc decide
-- Konkret sucht `decide` für eine Aussage `P`  nach einer Instanz `Decidable P`
-- welche dann evaluiert entweder wahr oder falsch rausgibt.

/--
Mit `unfold F` kannst du die Definition `F` im Beweisziel ausschreiben.
Mit `unfold F at h` machst du das Gleiche, aber in der Annahme `h`.

Zwar sind Beweisziel oder Annahme vor und nach `unfold` definitionsgleich,
aber viele Taktiken (z.B. `push_neg` oder `rw`) operieren auf einer syntaktischen Ebene,
sie „sehen nicht durch Definitionen hindurch“.

## Freunde und Verwandte

Die Taktiken `unfold F` und `simp only [F]` machen praktisch das Gleiche.
-/
TacticDoc unfold
-- * `change _` ist eine andere Taktik (nicht im Spiel), die das aktuelle Beweisziel in einen definitionsgleichen Ausdruck
--  umschreibt. Diese Taktik braucht man auch manchmal um zu hacken, wenn Lean Mühe hat etwas zu verstehen.

/--
Wenn das Beweisziel von der Form `∃x, P x` ist, kannst du mit `use n` ein konkretes Element angeben,
für das du `P x` beweisen möchtest.
-/
TacticDoc use

/--
Die Taktik `tauto` beweist logische Tautologien.

# Freunde und Verwandte

Manchmal muss das Beweisziel zuerst mit `generalize` abstrahiert werden, damit `tauto`  die Tautologie erkennt.
-/
TacticDoc tauto
