-- Level name : Rewrite

/-
Oft sind aber die Annahmen nicht genau das, was man zeigen will, sondern helfen einem
nur, dorthin zu kommen.

Wenn man eine Annahme `(h : a = b)` hat, kann man mit `rw [h]` (oder `rewrite [h]`) das erste
`a` im Goal mit `b` ersetzen.
Mit `rw [←h]` (`←` tippt man mit `\l`) ersetzt man in der Gegenrichtung `b` mit `a`.

(PS: die kleinen Zahlen `h₁ h₂ h₃` werden in Lean oft verwendet und man schreibt diese mit
`\1`, `\2`, `\3`, …)
-/

/- Lemma : no-side-bar
Angenommen man hat `a = b`, `c = d` und `a = d`, zeige dass `b = c`.
-/
example (a b c d : ℕ) (h₁ : a = b) (h₂ : c = d) (h₃ : a = d) : b = c :=
begin
  rw [h₂, ←h₁],
  exact h₃,
end

/-
Man kann übrigens auch mit `rw` in einer anderen Annahme umschreiben:
Probier mal `rw h₁ at h₃` als erstes. Danach hast du `(h₃ : b = d)` als Annahme.

Im weiteren kann man mit `rw [h, h, g, f]` mehrere rewrites auf einmal machen.
-/




/- Tactic : rw/rewrite
Gegeben eine Annahme `(h : X = Y)`, `rw [h]` ersetzt `X` im Goal mit `Y`.
`rw [←h]` ersetzt in der anderen Richtung.

`rw [h] at g` wendet die Taktik auf eine Annahme `g` an anstatt auf das aktuelle Goal.
-/

