import GameServer.Commands

TacticDoc by_contra
"
`by_contra h` startet einen Widerspruchsbeweis.

## Details
Sei `P` das aktuelle Goal. `by_contra h` fügt eine neue Annahme `(h : ¬P)` hinzu
und setzt das Goal auf `False`.

Oft will man `by_contra` nutzen wenn das Goal von der Form `¬ P` ist.

## Hilfreiche Resultate

* `contradiction` schliesst den Widerspruchsbeweis wenn sich (zwei) Annahmen
widersprechen.
* `contrapose` führt einen Beweis durch Kontraposition und ist entsprechend
in ähnlichen Situationen nutzbar wie `by_contra`
"

TacticDoc change
"
`change t` ändert das Goal zu `t`. Voraussetzung ist, dass `t` und das alte Goal defEq sind.

## Details

Dies ist insbesonder hilfreich wenn eine Taktik nicht merkt, dass das Goal defEq ist zu einem
Term, der eigentlich gebraucht würde.

## Beispiel

Aktuelles Goal:

```
b: ℝ
⊢ 1 • b = b
```
Wobei die Skalarmultiplikation als `fun (a : ℚ) (r : ℝ) => ↑a * r` definiert war. Dann
kann man mit `change (1 : ℚ) * b = b` das Goal umschreiben und anschliessend mit Lemmas
über die Multiplikation beweisen.
"



TacticDoc contrapose
"
`contrapose` ändert ein Goal der Form `A → B` zu `¬B → ¬A` und führt damit
eine Beweis durch Kontraposition.

## Hilfreiche Resultate

* `revert h` kann nützlich sein um eine Annahme als Implikationsprämisse zu schreiben bevor man
  `contrapose` verwendet.
"

TacticDoc exact
"
`exact h` schliesst das Goal wenn der Term `h` mit dem Goal übereinstimmt.
"

TacticDoc fin_cases
"
`fin_cases i` führt eine Fallunterscheidung wenn `i` ein endlicher Typ ist.

## Details
`fin_cases i` ist insbesondere nützlich für `(i : Fin n)`, zum Beispiel als Index in
endlich dimensionalen Vektorräumen.

In diesem Fall bewirkt `fin_cases i` dass man Komponentenweise arbeitet.
"

TacticDoc funext
"
`funext x` wird bei Gleichungen von Funktionen `f = g` gebraucht. Das Goal wird zu
`f x = g x`.

## Details
Nach dem Motto `f = g ↔ ∀ x, f x = g x` sind zwei Funktionen dann identisch, wenn sie
angewendet auf jedes Element identisch sind. `funext x` benützt dieses Argument.
"

TacticDoc «have»
"
`have h : P` führt ein Zwischenresultat ein.

## Details
Anschliessend muss man zuerst dieses Zwischenresultat beweisen bevor man mit dem Beweis
weitermachen und das Zwischenresultat verwenden kann.

## Hilfreiche Resultate

* `suffices h : P` funktioniert genau gleich, aussert das die beiden entstehenden Beweise
  vertauscht sind.
* `let h : Prop := A ∧ B` ist verwandt mit `have`, mit Unterschied, dass man mit `let`
  eine temporäre Definition einführt.
"

TacticDoc induction
"
`induction n` führt einen Induktionsbeweis über `n`.

## Detail

Diese Taktik erstellt zwei Goals:
* Induktionsanfang, wo `n = 0` ersetzt wird.
* Induktionsschritt, in dem man die Induktionshypothese `n_ih` zur Verfügung hat.

## Modifikationen in diesem Spiel

* `induction n with d hd` benennt Induktionsvariable und -hypothese. (das ist Lean3-Syntax)
und funktioniert ausserhalb vom Spiel nicht genau so.
* Ausserhalb des Spiels kriegst du `Nat.zero` und `Nat.succ n` anstatt `0` und `n + 1`
als Fälle. Diese
Terme sind DefEq, aber manchmal benötigt man die lemmas `zero_eq` und `Nat.succ_eq_add_one`
um zwischen den schreibweisen zu wechseln

Der richtige Lean4-Syntax für `with` streckt sich über mehrere Zeilen und ist:

```
induction n with
| zero =>
  sorry
| succ m m_ih =>
  sorry
```

da dieser sich über mehrere Zeilen erstreckt wird er im Spiel nicht eingeführt.

## Hifreiche Resultate

* `Nat.succ_eq_add_one`: schreibt `n.succ = n + 1` um.
* `Nat.zero_eq`: schreibt `Nat.zero = 0` um.

Beide sind DefEq, aber manche Taktiken können nicht damit umgehen

* Siehe Definition `∑` für Hilfe mit Induktion über Summen.
* `rcases n` ist sehr ähnlich zu `induction n`. Der Unterschied ist, dass bei
`rcases` keine Induktionshypothese im Fall `n + 1` zur Verfügung steht.

## Beispiel

```
example (n : ℕ) : 4 ∣ 5^n + 7 := by
  induction n
  sorry      -- Fall `n = 0`
  sorry      -- Fall `n + 1`
```
"

TacticDoc «let»
"
`let x : ℕ := 5 ^ 2` führt eine neue temporäre Definition ein.

## Hilfreiche Resultate

* `have x : ℕ := 5 ^ 2` führt ebenfalls eine neue natürliche Zahle `x` ein, aber
  Lean vergisst sofort, wie die Zahl definiert war. D.h. `x = 25` wäre dann nicht
  beweisbar. Mit `let x : ℕ := 5 ^ 2` ist `x = 25` durch `rfl` beweisbar.
"

TacticDoc linarith
"
`linarith` löst Systeme linearer (Un-)Gleichungen.

## Detail
`linarith` kann lineare Gleichungen und Ungleichungen beweisen indem
es das Gegenteil vom Goal annimmt und versucht einen Widerspruch in den
Annahmen zu erzeugen (Widerspruchsbeweis). Es braucht ein `≤` definiert um
zu funktionieren.

## Beispiel

Folgendes kann `linarith` beweisen.
```
Objekte
  x y : ℤ
  h₁ : 5 * y ≤ 35 - 2 * x
  h₂ : 2 * y ≤ x + 3
Goal
  y ≤ 5
```
"

TacticDoc refine
"
`refine { ?..! }` wird benötigt um eine Struktur (z.B. ein $R$-Modul) im Taktikmodus in einzelne
Goals aufzuteilen. Danach hat man ein Goal pro Strukturfeld.

(*Bemerkung*: Es gibt in Lean verschiedenste bessere Varianten dies zu erreichen,
z.B. \"Term Modus\" oder \"anonyme Konstruktoren\", aber für den Zweck des Spieles bleiben wir
bei diesem Syntax.)
"



TacticDoc simp
"
`simp` versucht alle Vereinfachungslemmas anzuwenden, die in der `mathlib` mit `@[simp]`
gekennzeichnet sind.

## Details

* `simp?` zeigt welche Lemmas verwendet wurden.
* `simp [my_lemma]` fügt zudem `my_lemma` temporär zur Menge der `simp`-Lemmas hinzu.
* ein `simp`, das nicht am Ende des Beweis steht sollte durch eine entsprechende
  `simp only [...]` Aussage ersetzt werden, um den Beweis stabiler zu machen.
"

TacticDoc simp_rw
"
`simp_rw [h₁, h₂, h₃]` versucht wie `rw` jedes Lemma der Reihe nach zu Umschreiben zu verwenden,
verwendet aber jedes Lemma so oft es kann.

## Details

Es bestehen aber drei grosse Unterschiede zu `rw`:

* `simp_rw` wendet jedes Lemma so oft an wie es nur kann.
* `simp_rw` kann besser unter Quantifiern umschreiben als `rw`.
* `simp_rw` führt nach jedem Schritt ein `simp only []` aus und vereinfacht dadurch grundlegenste
  Sachen.
"

TacticDoc «suffices»
"
`suffices h : P` führt ein neues Zwischenresultat ein, aus dem das Goal direkt folgen soll.

## Details

Der einzige Unterschied zu `have h : P` ist, dass die beiden resultierenden Goals vertauscht sind.

Mathematisch braucht man diese in ein bisschen unterschiedlichen Fällen:

* `suffices h : P` : \"Es genügt zu zeigen, dass …\". Als erstes folgt die Erklärung wieso
  das genügt, danach muss man nur noch `P` beweisen.
* `have h : P` : Ein (kleines) Zwischenresultat. Als erstes folgt dann der Beweis dieses
Resultats, anschliessend setzt man den Beweis mit Hilfe des Zwischenresultats fort.
"
