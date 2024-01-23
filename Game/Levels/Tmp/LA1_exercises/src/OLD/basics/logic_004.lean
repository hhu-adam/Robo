-- Level name : Widerspruch.

/-
Es gibt verschiedene Wege, wie man per Widerspruch argumentieren kann:

- `exfalso` ersetzt einfach das aktuelle Goal mit `false`. Jetzt muss man `false` zeigen.
- `by_contradiction h` ersetzt das Goal auch mit `false`, aber man kriegt eine neue Annahme
  `h`, welche die Kontraposition des alten Goals war.
- `contradiction` sucht in allen Annahmen zwei, die genau das gegenteilige sagen und
  schliesst den Beweis. Alternativ, kann man mit `exact absurd h not_h` genau das gleiche
  erreichen. (siehe links für die Beschreibung des Lemmas `absurd: A → ¬ A → B`.)

`by_contradiction h` ist eigentlich immer der go-to.
-/

/- Hint : Widerspruch
Sobald du ein Goal der Art `¬ A` hast, willst du häufig `by_contradiction ha` verwenden.
-/


/- Hint : Schluss
Schliessen kannst du einen Widerspruch indem du entweder mit `have` ein Zwischenresultat erstellst,
das einer anderen Annahme direkt widerspricht (dann mit `contradiction` schliessen), oder,
dass du mit `(exact absurd h not_h)` dies explizit angibst.
-/

/- Lemma :
Zeige folgende Kontraposition.
-/
lemma not_imp_not (A B : Prop) : (A → B) ↔ (¬B → ¬A) :=
begin
  constructor,
  { intros h b,
    by_contradiction a,
    exact absurd (h a) b },
  { intros h a,
    by_contradiction b,
    have a' := h b,
    contradiction }
end

/- Tactic : by_contradiction/exfalso
`by_contradiction h` nimmt an das Gegenteil vom Goal sei wahr und gibt diesem den Namen `h`.
`exfalso` macht das gleiche ohne `h` zu speichern.
-/

/- Tactic : contradiction
Schliesst einen Beweis, wenn zwei gegensätzliche Annahmen existieren. Gleiches wird mit
`exact absurd ha hb` erreicht.
-/

/- Axiom : absurd
`absurd : A → ¬A → B`. Aus `A` und `¬A` kann man alles beweisen.
-/
