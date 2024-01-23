-- Level name : Definitionally equal

/-
Achtung: `refl` kann auch Gleichungen beweisen, wenn die beiden Terme Lean-intern gleich definiert sind,
auch wenn diese unterschiedlich dargestellt werden.
so sind `1 + 1` und `2` per Definition das Gleiche, da sie beide von Lean als `0.succ.succ` gelesen werden.

Das kann anfänglich verwirrend sein und das Verhalten hängt von der Lean-Implementation ab. 
-/

/- Lemma : no-side-bar
Beweise
-/
example : 1 + 1 = 2 :=
begin
  refl,
end

/-
Im weiteren führen die meisten anderen Taktiken `refl` automatisch am Ende aus,
deshalb musst du dieses häufig gar nicht mehr schreiben.
-/