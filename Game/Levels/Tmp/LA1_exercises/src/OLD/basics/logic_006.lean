-- Level name : Automatisierung

import tactic.tauto

variables (A B : Prop)

/-
Eine Stärke von Lean ist, dass man Automatisierung hat, die einem hilft, "Trivialitäten"
schnell rigorous zu beweisen.

Für Prädikat-Logik hilft die `tauto`-Taktik weiter, welche alle bisherigen Übungsaufgaben
direkt lösen kann.
-/


/- Lemma :
Beweise Aufgabe 4 nochmals mit einem Einzeiler.
-/
lemma or_iff_not_imp_left' : (A ∨ B) ↔ (¬ A → B) :=
begin
  tauto,
end

/- Hint : Law-of-excluded-middle
`tauto!` ist noch ein bisschen stärker als `tauto` indem
es das Law-of-excluded-middle aktiv benutzt.

(Oben reicht `tauto`, weil es ein Statement in der Library findet
so dass es das Law-of-excluded-middle nicht selber
ausführen muss.)
-/

/- Tactic : tauto
Kann Aussagenlogik automatisch beweisen.

`tauto!` ist noch eine stärkere Version.
-/
