import GameServer.Commands

/--
Sind eine Annahme `h : A` und eine Implikation `hAB : A → B` gegeben, so
verwandelt `apply hAB at h` die gegebene Annahme in die Annahme `h : B`.
Ist `B` unser Beweisziel, können wir mit `apply hAB` auch rückwärts argumentieren und
erhalten `A` als neues Beweisziel.   In beiden Fällen kann die Implikation `hAB` wahlweise
als Annahme gegeben oder ein bereits bekanntes Lemma sein.


## Beispiel

Gegeben sei für `n : ℕ` folgendes Lemma:
```
lemma lem (h : n ≤ 0) : n = 0
```

Finden wir nun als Beweisziel

```
Goal
  n = 0
```

vor, so ändert `apply lem` das Beweisziel zu `n ≤ 0`.

Anders herum, falls wir eine Annahme `g : m ≤ 0` in unseren Annahmen finden, können wir
diese mit `apply lem at g` zu `g : m = 0` umwandeln.

(Das Lemma ist gemeinhin als `Nat.eq_zero_of_le_zero` bekannt.)
-/
TacticDoc apply



/--
`assumption` sucht nach einer Annahme, die genau dem Goal entspricht.

## Beispiel

`assumption` sucht durch die Annahmen und merkt dass `h` genau mit dem Goal übereinstimmt.

```
Objekte
  a b c d : ℕ
  h : a + b = c
  g : a * b = 16
  t : c = 12
Goal
  a + b = c
```
-/
TacticDoc assumption



/--
`by_cases h : P` macht eine Fallunterscheidung. Im ersten Goal wird eine Annahme
`(h : P)` hinzugefügt, im zweiten `(h : ¬P)`.

## Details

`P` kann eine beliegige Aussage sein, die als entweder wahr oder falsch angenommen wird.

## Beispiel

```
example (A : Prop) : A ∨ ¬ A := by
  by_cases h : A
  · left
    assumption
  · right
    assumption
```
-/
TacticDoc by_cases



/--
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
-/
TacticDoc by_contra



/--
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
-/
TacticDoc change



/--
`constructor` teilt ein Beweisziel, das eine Struktur ist, in seine Bestandteile auf.

## Detail
Übliche Anwendungsfälle sind Beweisziele der Form `A ∧ B` sowie Äquivalenzen, also Beweisziele der Form `A ↔ B`.
Im ersten Fall ersetzt `constructor` das Ziel `A ∧ B` durch die zwei Ziel `A` and `B`, im zweiten Fall ersetzt `constructor` die Äquivalenz durch die beiden Beweisziele `A → B` and `B → A`.

## Hilfreiche Resultate

* Das Gegenteil von `constructor` ist `⟨_, _⟩` (`\\<>`), der *anonyme Konstruktor*.
Dieser enspricht ungefähr der Tupel-Notation in
\"eine Gruppe ist ein Tupel $(G, 0, +)$, sodass …\".

## Beispiel

```
example {A B : Prop} (h : A) (g : B) : A ∧ B := by
  constructor
  · assumption
  · assumption
```
-/
TacticDoc constructor



/--
`contradiction` schliesst den Beweis wenn es einen Widerspruch in den Annahmen findet.

## Details
Ein Widerspruch in den Annahmen kann unter anderem folgendermaßen aussehen:

* `(h : n ≠ n)`
* `(h : A)` und `(h' : ¬A)`
* `(h : False)` (i.e. ein Beweis von `False`)

## Beispiel

Folgenes Goal wird von `contradiction` bewiesen

## Hilfreiche Resultate

* Normalerweise wird `contradiction` gebraucht um einen Widerspruchsbeweis zu
  schliessen, der mit `by_contra` eröffnet wurde.
* Ein Beweis von `False` representiert in Lean einen Widerspruch.

```
Objekte:
  (n m : ℕ)
  (h : n = m)
  (g : n ≠ m)
Goal
  37 = 60
```
nach dem Motto \"ein Widerspruch beweist alles.\"
-/
TacticDoc contradiction



/--
`contrapose` ändert ein Goal der Form `A → B` zu `¬B → ¬A` und führt damit
eine Beweis durch Kontraposition.

## Hilfreiche Resultate

* `revert h` kann nützlich sein um eine Annahme als Implikationsprämisse zu schreiben bevor man
  `contrapose` verwendet.
-/
TacticDoc contrapose



/--
`exact h` schliesst das Goal wenn der Term `h` mit dem Goal übereinstimmt.
-/
TacticDoc exact



/--
`fin_cases i` führt eine Fallunterscheidung wenn `i` ein endlicher Typ ist.

## Details
`fin_cases i` ist insbesondere nützlich für `(i : Fin n)`, zum Beispiel als Index in
endlich dimensionalen Vektorräumen.

In diesem Fall bewirkt `fin_cases i` dass man Komponentenweise arbeitet.
-/
TacticDoc fin_cases



/--
`funext x` wird bei Gleichungen von Funktionen `f = g` gebraucht. Das Goal wird zu
`f x = g x`.

## Details
Nach dem Motto `f = g ↔ ∀ x, f x = g x` sind zwei Funktionen dann identisch, wenn sie
angewendet auf jedes Element identisch sind. `funext x` benutzt dieses Argument.
-/
TacticDoc funext



/--
`have h : P` führt ein Zwischenresultat ein.

## Details
Anschliessend muss man zuerst dieses Zwischenresultat beweisen bevor man mit dem Beweis
weitermachen und das Zwischenresultat verwenden kann.

## Hilfreiche Resultate

* `suffices h : P` funktioniert genau gleich, außer dass die beiden entstehenden Beweise
  vertauscht sind.
* `let h : Prop := A ∧ B` ist verwandt mit `have`, mit Unterschied, dass man mit `let`
  eine temporäre Definition einführt.
-/
TacticDoc «have»



/--
`induction n` führt einen Induktionsbeweis über `n`.

## Detail

Diese Taktik erstellt zwei Goals:
* Induktionsanfang, wo `n = 0` ersetzt wird.
* Induktionsschritt, in dem man die Induktionshypothese `n_ih` zur Verfügung hat.

## Modifikationen in diesem Spiel

* `induction n with d hd` benennt Induktionsvariable und -hypothese. (das ist Lean3-Syntax)
und funktioniert außerhalb vom Spiel nicht genau so.
* Außerhalb des Spiels kriegst du `Nat.zero` und `Nat.succ n` anstatt `0` und `n + 1`
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
-/
TacticDoc induction



/--
`intro x` wird für Goals der Form `A → B` oder `∀ x, P x` verwendet.
Dadurch wird die Implikationsprämisse (oder das Objekt `x`) den Annahmen hinzugefügt.

## Hilfreiche Resultate

* `revert h` macht das Gegenteil von `intro`.
-/
TacticDoc intro



/--
Wenn das Goal von der Form `A ∨ B` ist, enscheidet man mit `left` die linke Seite zu zeigen.

## Hilfreiche Resultate

* `right` entscheidet sich für die linke Seite.
-/
TacticDoc left



/--
`let x : ℕ := 5 ^ 2` führt eine neue temporäre Definition ein.

## Hilfreiche Resultate

* `have x : ℕ := 5 ^ 2` führt ebenfalls eine neue natürliche Zahle `x` ein, aber
  Lean vergisst sofort, wie die Zahl definiert war. D.h. `x = 25` wäre dann nicht
  beweisbar. Mit `let x : ℕ := 5 ^ 2` ist `x = 25` durch `rfl` beweisbar.
* `set x : ℕ := 5 ^ 2` macht das Gleiche wie `let` aber versucht auch `x` im Goal überall einzusetzen wo `5 ^ 2` steht.
-/
TacticDoc «let»

/--
`set f := _` funktioniert wie `let` aber versucht auch `f` im Goal überall einzusetzen.
-/
TacticDoc set

/--
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
-/
TacticDoc linarith



/--
`push_neg` schreibt `¬∀ x, _` zu `∃ x, ¬ _` und `¬∃ x, _` zu `∀x, ¬ _` um.

## Details

`push_neg` schiebt das `¬` soweit nach innen wie möglich.

## Hilfreiche Resultate

* Die beiden Lemmas heissen `not_forall` und `not_exists` und können mit `rw` einzeln angewendet
  werden.
-/
TacticDoc push_neg



/--
`rcases h` teilt eine Annahme `h` in ihre Einzelteile auf.

## Details
Für Annahmen die Strukturen sind, wie z.B. `h : A ∧ B` (oder `∃x, P x`) kann man die
Einzelteile mit  `rcases h with ⟨a, b⟩` (oder `rcases h with ⟨x, hx⟩`) benennen.

Für eine Annahme der Form `h : A ∨ B` kann man mit `rcases h with ha | hb` zwei Goals
erzeugen, einmal unter Annahme der linken Seite, einmal unter Annahme der Rechten.

## Hilfreiche Resultate

* Für `n : ℕ` hat `rcases n` einen ähnlichen Effekt wie `induction n` mit dem Unterschied,
  dass im Fall `n + 1` keine Induktionshypothese zur Verfügung steht.
* In Lean gibt es auch die Taktik `cases`, die gleich funktioniert wie `rcases` aber
  einen mehrzeiligen Syntax hat:
  ```
  cases h with
  | inl ha =>
    sorry
  | inr hb =>
    sorry
  ```
  Hier sind `inl`/`inr` die Namen der Fälle und `ha`/`hb` sind frei gewählte Namen für die
  freien Variablen
-/
TacticDoc rcases

-- TODO:
/-- obtain ⟨arg1, arg2⟩ := h decomposes `h` to its parts `arg1` and `arg2`-/
TacticDoc obtain


/--
`refine { ?..! }` wird benötigt um eine Struktur (z.B. ein $R$-Modul) im Taktikmodus in einzelne
Goals aufzuteilen. Danach hat man ein Goal pro Strukturfeld.

(*Bemerkung*: Es gibt in Lean verschiedenste bessere Varianten dies zu erreichen,
z.B. \"Term Modus\" oder \"anonyme Konstruktoren\", aber für den Zweck des Spieles bleiben wir
bei diesem Syntax.)
-/
TacticDoc refine

/--
`refine' { .. }` wird benötigt um eine Struktur (z.B. ein $R$-Modul) im Taktikmodus in einzelne
Goals aufzuteilen. Danach hat man ein Goal pro Strukturfeld.

(*Bemerkung*: Es gibt in Lean verschiedenste bessere Varianten dies zu erreichen,
z.B. \"Term Modus\" oder \"anonyme Konstruktoren\", aber für den Zweck des Spieles bleiben wir
bei diesem Syntax.)
-/
TacticDoc refine'

/--
`revert h` fügt die Annahme `h` als Implikationsprämisse vorne ans Goal an.

## Hilfreiche Resultate

* `revert` ist das Gegenteil von `intro`.
* `revert` kann insbesondere nützlich sein, um anschliessend `contrapose` zu verwenden.

## Beispiel

```
Objekte
  A P : Prop
  h : P
Goal
  A
```

hier ändert `revert h` den Status zu

```
Objekte
  A P : Prop
Goal
  P → A
```
-/
TacticDoc revert



/--
`rfl` beweist ein Goal der Form `X = X`.

## Detail

`rfl` beweist jedes Goal `A = B` wenn `A` und `B` per Definition das gleiche sind (DefEq).
Andere Taktiken rufen `rfl` oft am Ende versteckt
automatisch auf um zu versuchen, den Beweis zu schliessen.


## Beispiel
`rfl` kann folgende Goals beweisen:

```
Objekte
  a b c : ℕ
Goal:
  (a + b) * c = (a + b) * c
```

```
Objekte
  n : ℕ
Goal
  1 + 1 = 2
```
denn Lean liest dies intern als `0.succ.succ = 0.succ.succ`.
-/
TacticDoc rfl



/--
Wenn das Goal von der Form `A ∨ B` ist, enscheidet man mit `right` die rechte Seite zu zeigen.

## Hilfreiche Resultate

* `left` entscheidet sich für die linke Seite.
-/
TacticDoc right



/--
Löst Gleichungen mit den Operationen `+, -, *, ^`.

## Details
Insbesondere funktioniert `ring` in Ringen/Semiringen wie z.B. `ℕ, ℤ, ℚ, …`
(i.e. Typen `R` mit Instanzen `Ring R` oder `Semiring R`).
Die Taktik ist besonders auf kommutative Ringe (`CommRing R`) ausgelegt.

## Hilfreiche Resultate

* `ring` kann nicht wirklich mit Division (`/`) oder Inversen (`⁻¹`) umgehen. Dafür ist die
  Taktik `field_simp` gedacht, und die typische Sequenz ist
  ```
  field_simp
  ring
  ```
-/
TacticDoc ring



/--
Wenn man eine Annahme `(h : X = Y)` hat, kann man mit
`rw [h]` alle `X` im Goal durch `Y` ersetzen.

## Details

* `rw [←h]` wendet `h` rückwärts an und ersetzt alle `Y` durch `X`.
* `rw [h, g, ←f]`: Man kann auch mehrere `rw` zusammenfassen.
* `rw [h] at h₂` ersetzt alle `X` in `h₂` zu `Y` (anstatt im Goal).

`rw` funktioniert gleichermaßen mit Annahmen `(h : X = Y)` also auch
mit Theoremen/Lemmas der Form `X = Y`
-/
TacticDoc rw



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



/--
`suffices h : P` führt ein neues Zwischenresultat ein, aus dem das Goal direkt folgen soll.

## Details

Der einzige Unterschied zu `have h : P` ist, dass die beiden resultierenden Goals vertauscht sind.

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

ist das Goal `x = y`, dann wandelt es `symm` in `y = x` um. Analog, wandelt `symm at h` die Annahme
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

Genauso wie für Gleichungen `X = Z` funktioniert `trans` auch für Äquivalenzen `X ↔ Z` und gewisse transitive Relationen im Beweisziel.
-/
TacticDoc trans

/--
`trivial` versucht durch Kombination von wenigen simplen Taktiken das Goal zu schliessen.

## Details
Die Taktiken, die verwendet werden sind:

* `assumption`
* `rfl`
* `contradiction`
* und noch 3 andere, die hier nicht behandelt werden
  (`decide`, `apply True.intro`, `apply And.intro`).
-/
TacticDoc trivial



/--
`unfold myDef` öffnet eine Definition im Goal.

## Details
Bis auf DefEq (definitinal equality) ändert `unfold` nichts, manche Taktiken
(z.B. `push_neg`, `rw`) brauchen aber manchmal die Hilfe.

`unfold myDef at h` kann auch Definitionen in Annahmen öffnen

## Hilfreiche Resultate

* `change P` ist eine andere Taktik, die das aktuelle Goal in einen DefEq-Ausdruck umschreibt.
  Diese Taktik braucht man auch manchmal um zu hacken, wenn Lean Mühe hat etwas zu verstehen.
-/
TacticDoc unfold



/--
Wenn das Goal von der Form `∃x, P x` ist, kann man mit `use n` ein konkretes Element angeben
mit dem man das Goal beweisen möchte.

## Details

`use n` versucht zudem anschliessend `rfl` aufzurufen, und kann das Goal damit manchmal direkt
schließen.
-/
TacticDoc use

/-- `tauto` proves all logical tautologies.-/
TacticDoc tauto
