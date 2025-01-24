-- Level name : Aller Anfang ist... ein Einzeiler?

/-
Willkommen zum Lean-Crashkurs wo du lernst wie man mathematische Beweise vom Computer
unterstützt und verifiziert schreiben kann.

Ein Beweis besteht in Lean aus verschiedenen **Taktiken**, welche ungefähr einem
logischen Schritt entsprechen, den man auf Papier aufschreiben würde.

Rechts im **Infoview** siehst den Status des aktuellen Beweis.
Du siehst ein oder mehrere offene **Goals** (mit einem `⊢` davor), die du noch zeigen musst.
Wenn du eine Taktik hinschreibst (Lean 3 : Komma am Ende), dann versucht Lean diesen Schritt beim
ersten offenen Goal zu machen.
Wenn der Beweis komplett ist, erscheint "goals accomplished".

Die erste Taktik ist `refl`, die ein Goal von der Form `A = A` beweist.
-/

/- Lemma : no-side-bar
In den natürlichen Zahlen gilt `42 = 42`.
-/
example : 42 = 42 :=
begin
  refl,
end

/- Tactic : refl
Schliesst ein Goal von der Form `A = A`.
(Hängt davon ab, dass die beiden Seiten in Lean intern gleich definiert sind, auch
wenn diese anders dargestellt werden. z.B. sind `1 + 1` und `2` per Definition gleich in Lean.)
-/