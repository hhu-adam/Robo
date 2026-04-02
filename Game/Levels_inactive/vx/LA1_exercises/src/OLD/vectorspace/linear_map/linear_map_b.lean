-- Level name : Linear Maps

-- begin hide
import vectorspace.linear_map.linear_map
-- end hide

/-
Das Skelet unserer linearen Abbildung sieht dann so aus:

```
def f :  ℝ² →ₗ[ℝ] ℝ² :=
  { to_fun := f_map,
    map_add' := f_map_add,
    map_smul' := _,
    end }
```

Jetzt müssen wir noch die beiden linearen Eigenschaften zeigen.
-/

/- Lemma : no-side-bar
Zeige dass `f` mit der Skalarmultiplikation kommutiert.
-/
lemma f_map_smul : ∀ (r : ℝ) (v : ℝ²), f_map (r • v) = r • (f_map v) :=
begin
  -- Dieser Beweis verläuf exakt analog zu oben, der einzige Unterschied ist
  -- die konkrete Rechnung am Schluss, und die übernimmt `ring` für dich.
  intros,
  apply funext,
  intro i,
  fin_cases i,
  { unfold f_map,
    -- Bemerkung: Wenn du jetzt `simp` brauchst, macht es sogar noch mehr als vorher.
    -- Skalarmultiplikation ist einfach als komponentenweise Multiplikation definiert.
    -- Entsprechend braucht `simp` ein Lemma `smul_eq_mul : a • b = a * b`.
    simp,
    ring },
  { unfold f_map,
    simp,
    ring }
end

/-
Mit den beiden Beweisen können wir nun eine lineare Abbildung definieren, die diese
Beweise dann gebündelt hat.
-/
def f : ℝ² →ₗ[ℝ] ℝ² :=
{ to_fun := λ v, ![5 * (v 1) + 2 * (v 2), (v 1) - (v 2)],
  map_add' := f_map_add,
  map_smul' := f_map_smul }
