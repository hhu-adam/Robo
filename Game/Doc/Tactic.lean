import GameServer.Commands

/--
Sind eine Annahme `h : A` und eine Implikation `hAB : A → B` gegeben, so
verwandelt `apply hAB at h` die gegebene Annahme in die Annahme `h : B`.
Ist `B` dein Beweisziel, kannst du mit `apply hAB` auch rückwärts argumentieren und
erhältst `A` als neues Beweisziel.

In beiden Fällen kann die Implikation `hAB` wahlweise
als Annahme gegeben oder ein bereits bekanntes Lemma sein.
-/
TacticDoc apply

/--
`assumption` sucht nach einer Annahme, die genau dem Beweisziel entspricht.
-/
TacticDoc assumption

/--
`by_cases h : P` macht eine Fallunterscheidung, ob `P` wahr oder falsch ist.
Zum beispiel unterscheided `by cases h : a = b` die Fälle `a = b` und `a ≠ b`.

Das Beweisziel wird hierzu dupliziert, und
in der ersten „Kopie“ wird die Annahme `(h : P)` hinzugefügt,
in der zweiten „Kopie“ die Annahme `(h : ¬P)`.
-/
TacticDoc by_cases

/--
`by_contra h` startet einen Widerspruchsbeweis.
Ist `P` das aktuelle Beweisziel, so generiert `by_contra h` eine neue Annahme `(h : ¬P)`
und setzt das Beweisziel auf `False`.

Oft will man `by_contra` nutzen, wenn das Beweisziel von der Form `¬ P` ist.

## Freunde und Verwandte

* Am Ende eines Widerspruchsbweises braucht man gewöhnlich `contradiction`:
diese Taktik schließt den Besweis, wenn sie zwei offensichtlich widersprüchlichen Annahmen.
* Ist das Beweiszeil von der Form `A → B`, kannst du mit `contrapose`
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
Eine Annahme der Form `h : ∃ b : B, P b` kannst du mit
`choose b hb using h` in die Bestandteile `b : A` und `hb : P b`
zerlegen.

Allgemeiner kannst du `choose` verwenden, um Elemente mit dem Auswahlaxiom zu wählen:
aus einer Annahme der Form `h : ∀ a, ∃ b, P a b` extrahiert `choose f hf using h`
eine Abbildung `f : A → B` und die Aussage ` ∀ (a : A), P a (f a)`.
(Hier ist `P : A → (B → Prop)` ein Prädikat, das von zwei Variablen `a` und `b` abhängt.)
 -/
TacticDoc choose


/--
Die Taktik `constructor` teilt ein Beweisziel in seine Bestandteile auf:

| Ausgangslage | Resultat                |
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
eine Beweis durch Kontraposition ein.

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
x ∈ A ↔ x ∈ B.
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
f x = g x.
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
Mit `induction n with d dh` kannst du Namen für die Induuktionsvariable (hier: `d`)
und die Induktionsannahme (hier: `hd`) vorgeben.
Die Taktik ersetzt also das ursprüngliche Beweiszeil durch zwei neue Beweisziele:
* einen Induktionsanfang, in dem `n = 0` ersetzt wird
* einen Induktionsschritt, in dem du die Induktionsannehme `hd` zur Verfügung steht.

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

## Freunde und Verwandte

Die Taktik `revert` macht genau das Gegenteil von `intro`.
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
Die (Un)Gleichungen müssen aber gut lesbar gegeben sein -- eine Annahme der Form
```
m ≤ x → n < x
```
muss beispielsweise erst mit
```
rw [imp_iff_or_not] at h
```
zu
```
hx : n < x ∨ ¬m ≤ x
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
Die Taktik `push_neg` schreibt `¬∀ x, _` zu `∃ x, ¬ _` und `¬∃ x, _` zu `∀x, ¬ _` um.
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

| Ausgangslage       | Taktik                 | Resultat                                   |
|:------------------ |:---------------------- |:------------------------------------------ |
| `h : A ∧ B`        | `obtain ⟨hA, hB⟩ := h` | `hA : A` und `hB : B`                      |
| `h : A ↔ B`        | `obtain ⟨hl, hr⟩ := h` | `hl : A → B` und `hr : B → A`              |
| `h : Nonempty X`   | `obtain ⟨x⟩ := h`      | `x : X`                                    |
| `h : ∃ x : X, P x` | `obtain ⟨x, hx⟩ := h`  | `x : X` und `hx : P x`                     |
| `h : A ∨ B`        | `obtain h \| h := h`   | ein Ziel mit `h : A`, ein Ziel mit `h : B` |

Die Klammern in den ersten vier Beispielen tippst du als `\<` bzw. `\>`.
Hier ist `⟨_, _⟩` der *anonyme Konstruktor*.
Man kann ihn sich ungefähr so vorstellen wir die Tupel-Notation in
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

Die Taktik `intro` macht das genaue Gegenteil von `revert`.
-/
TacticDoc revert


/--
`rfl` beweist `X = X`.  Genauer schließt `rfl` jedes Beweisziel der Form `A = B`,
in dem `A` und `B` definitionsgleich sind.
-/
TacticDoc rfl
-- rfl beweist auch 1 + 1 = 2 in ℕ, denn intern sind beide Seiten `0.succ.succ`.

/--
Wenn das Beweisziel von der Form `A ∨ B` ist, enscheidestt du dich mit `right`, die rechte Seite zu zeigen.

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
--
-- * `ring` kann nicht wirklich mit Division (`/`) oder Inversen (`⁻¹`) umgehen. Dafür ist die
--  Taktik `field_simp` gedacht, und die typische Sequenz ist
--  ```
--  field_simp
--  ring
--  ```

/--
Wenn man eine Annahme `(h : X = Y)` hat, kann man mit
`rw [h]` alle `X` im Beweisziel durch `Y` ersetzen.

## Details

* `rw [←h]` wendet `h` rückwärts an und ersetzt alle `Y` durch `X`.
* `rw [h, g, ←f]`: Man kann auch mehrere `rw` zusammenfassen.
* `rw [h] at h₂` ersetzt alle `X` in `h₂` zu `Y` (anstatt im Beweisziel).
* `rw [my_theorem]` sucht nach dem ersten Ort, wo es umschreiben kann um die Impliziten
  Argumente von `my_theorem` zu füllen
* `nth_rw 2 [my_theorem]` ist eine Variante, die stattdessen am 2. Ort umschreibt.

`rw` funktioniert gleichermaßen mit Annahmen `(h : X = Y)` also auch
mit Theoremen/Lemmas der Form `X = Y`

## Beispiel

```
Objekte:
  m n : ℕ
  f g : ℕ → ℕ
Annahmen:
  h₁ : m = n
  h₂ : f = g
Beweisziel:
  f m = g n
```

`rw [h₂]` schreibt das Beweisziel zu `g n = g m` um, ein weiteres `rw [h₁]` dann zu `g m = g m`, was es
direkt auch schließt.

-/
TacticDoc rw

/-- (shouldn't be visible to the player!) -/
TacticDoc nth_rw

/--
`simp` versucht alle Vereinfachungslemmas anzuwenden, die in der `mathlib` mit `@[simp]`
gekennzeichnet sind.

## Details

* `simp?` zeigt welche Lemmas verwendet wurden.
* `simp [my_lemma]` fügt zudem `my_lemma` temporär zur Menge der `simp`-Lemmas hinzu.
* ein `simp`, das nicht am Ende des Beweis steht sollte durch eine entsprechende
  `simp only [...]` Aussage ersetzt werden, um den Beweis stabiler zu machen.
-/
TacticDoc simp



/--
`simp_rw [h₁, h₂, h₃]` versucht wie `rw` jedes Lemma der Reihe nach zu Umschreiben zu verwenden,
verwendet aber jedes Lemma so oft es kann.

## Details

Es bestehen aber drei grosse Unterschiede zu `rw`:

* `simp_rw` wendet jedes Lemma so oft an wie es nur kann.
* `simp_rw` kann besser unter Quantifiern umschreiben als `rw`.
* `simp_rw` führt nach jedem Schritt ein `simp only []` aus und vereinfacht dadurch grundlegenste
  Sachen.
-/
TacticDoc simp_rw


/-- `specialize h a₁ a₂` ist äquivalent zu `have h := h a₁ a₂`: es ersetzt eine Annahme
`h : ∀ m₁ m₂, P m₁ m₂` durch den Spezialfall `h : P a₁ a₂`.

Falls man mehrmals spezialisieren möchte, sollte man statt `specialize`
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
`suffices h : P` führt ein neues Zwischenresultat ein, aus dem das Beweisziel direkt folgen soll.

## Details

Der einzige Unterschied zu `have h : P` ist, dass die beiden resultierenden Beweisziels vertauscht sind.

Mathematisch braucht man diese in ein bisschen unterschiedlichen Fällen:

* `suffices h : P` : \"Es genügt zu zeigen, dass …\". Als erstes folgt die Erklärung wieso
  das genügt, danach muss man nur noch `P` beweisen.
* `have h : P` : Ein (kleines) Zwischenresultat. Als erstes folgt dann der Beweis dieses
Resultats, anschliessend setzt man den Beweis mit Hilfe des Zwischenresultats fort.
-/
TacticDoc «suffices»



/--
`symm` (für "symmetry") kann Gleichheiten oder `↔` umdrehen. `symm at h` dreht eine Gleichheit
(oder `↔`) in der Annahme `h`.

## Details

Man kann auch `h.symm` für die gedrehte Annahme schreiben, wenn man diese irgendwo
verwendet. Das verwendet intern die Lemmata
`Eq.symm` oder `Iff.symm`.

## Beispiel

ist das Beweisziel `x = y`, dann wandelt es `symm` in `y = x` um. Analog, wandelt `symm at h` die Annahme
`(h : z = w)` in `(h : w = z)` um.
-/
TacticDoc symm

/--
Wenn man `X = Z` zeigen möchte, kann man mit
`trans Y` einen Zwischenschritt `Y` einfügen.
Zu zeigen sind dann also `X = Y`  und `Y = Z`.

## Details
`trans` ist besondern gut geeignet, um eine Gleichung `X = Z `
durch eine „Rechnung“ der Form `X = Y₁ = Y₂ = Y₃ … = Z` Schritt für Schritt nachzuweisen:

* `trans Y₁`
* Beweis von `X = Y₁`
* `trans Y₂`
* Beweis von `Y₁ = Y₂`
* `trans Y₃`
* …
* Beweis von `… = Z`

Genauso wie für Gleichungen `X = Z` funktioniert `trans` auch für Äquivalenzen `X ↔ Z` und gewisse
transitive Relationen im Beweisziel.

## Beispiel

```
Objekte:
  A B C : Prop
Annahmen:
  h₁ : A ↔ B
  h₂ : B ↔ C
Beweisziel:
  A ↔ C
```

Die Taktik `trans B` erstellt dann aus dem Beweisziel zwei neue `A ↔ B` und `B ↔ C`.

-/

TacticDoc trans

/--
`decide` kann Aussagen beweisen, für die es einen einfachen Algorithmus
gibt, der die Wahr- oder Falschheit der Aussage bestimmt.

Wichtige Beispiele sind:

* `True`
* Aussagen zu konkreten Zahlen, wie `Even 4`, `2 ≤ 5`, `4 ≠ 6`, …


## Details

Konkret sucht `decide` für eine Aussage `P`  nach einer Instanz `Decidable P`
welche dann evaluiert entweder wahr oder falsch rausgibt.

## Beispiel

Folgendes kann mit `decide` gelöst werden:

```
Beweisziel:
  ¬ Odd 40
```
-/
TacticDoc decide



/--
`unfold myDef` öffnet eine Definition im Beweisziel.

## Details
Bis auf Definitionsgleichheit ändert `unfold` nichts, manche Taktiken
(z.B. `push_neg`, `rw`) brauchen aber manchmal die Hilfe.

`unfold myDef at h` kann auch Definitionen in Annahmen öffnen

## Freunde und Verwandte

* `unfold f` kann insbesondere nötig sein, wenn man danach `rw` benützt,
  da `rw` nicht durch Definitionen hindurch sieht.
* `unfold f` oder `simp only [f]` machen praktisch das Gleiche.
* Im Moment kennt Mathlib auch noch `unfold_let`: `unfold` ist für Definitionen, `unfold_let`
  für `let`-Statements.
* `change _` ist eine andere Taktik (nicht im Spiel), die das aktuelle Beweisziel in einen definitionsgleichen Ausdruck
  umschreibt. Diese Taktik braucht man auch manchmal um zu hacken, wenn Lean Mühe hat etwas zu verstehen.

## Beispiel

```
Beweisziel:
  Even 0
```

Auch wenn `rfl` dieses Beweisziel lösen kann, kann es nützlich sein `unfold Even` zu benützen um die
Definition hinter `Even` zu sehen.
-/
TacticDoc unfold



/--
Wenn das Beweisziel von der Form `∃x, P x` ist, kann man mit `use n` ein konkretes Element angeben
mit dem man das Beweisziel beweisen möchte.

## Details

`use n` versucht zudem anschliessend `rfl` aufzurufen, und kann das Beweisziel damit manchmal direkt
schließen.

## Beispiel

```
Beweisziel:
  ∃ x, x + 3 = 4
```

hier würde man `use 1` benützen.
-/
TacticDoc use

/--
`tauto` proves all logical tautologies.

## Beispiel

Folgendes Beweisziel ist mit `tauto` lösbar

```
Objekte:
  (A B C : Prop)
Beweisziel:
  ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C)
```
-/
TacticDoc tauto
