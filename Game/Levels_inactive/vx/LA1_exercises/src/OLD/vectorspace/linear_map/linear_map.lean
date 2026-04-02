-- Level name : Linear Maps

import data.real.basic           -- definiert `ℝ`
import algebra.module.linear_map -- definiert `→ₗ`
import data.matrix.notation

/-
Als erstes definieren wir wieder eine Notation für `ℝ²` und testen, dass Lean weiss, dass dies ein `ℝ`-Modul ist. 
-/
notation `ℝ²` := fin 2 → ℝ
example : module ℝ ℝ² := infer_instance

/-
Sei `R` ein Ring und `V W` zwei `R`-Moduln. Eine `R`-lineare Abbildung wird in Lean
folgendermassen geschrieben: `V →ₗ[R] W` (`\to` + `\_l`).

Man erstellt eine lineare Abbildung aus einer Funktion `f : V → W` zusammen mit den beweisen,
dass `f` Addition und Skalarmultiplikation erhält,
i.e. `f (x + y) = f x + f y` und `f (r • x) = r • f x`.

Hier definieren wir zum Beispiel die Null-Abbildung, die einfach alles auf `0` sendet:
-/


variables {R V W : Type*} [ring R] [add_comm_monoid V] [add_comm_monoid W] [module R V] [module R W]

def my_zero_map : V →ₗ[R] W :=
  { to_fun := λ x, 0,
    map_add' :=
    begin
      intros,
      simp,
    end,
    map_smul' :=
    begin
      intros,
      simp,
    end }

/-

## Aufgabe

Zeige dass die Abbildung

```
  ℝ² → ℝ²
  (x, y) ↦ (5x + 2y, x - y)
```

`ℝ`-linear ist. Dafür müssen wir zuerst die unterliegende Funktion angeben:
-/

def f_map : ℝ² → ℝ² := λ v, ![5 * (v 1) + 2 * (v 2), (v 1) - (v 2)]


/-
Das Skelet unserer linearen Abbildung sieht dann so aus:

```
def f :  ℝ² →ₗ[ℝ] ℝ² :=
  { to_fun := f_map,
    map_add' := _,
    map_smul' := _,
    end }
```

Jetzt müssen wir noch die beiden linearen Eigenschaften zeigen.
-/

/- Lemma : no-side-bar
Zeige dass `f` mit der Addition kommutiert.
-/
lemma f_map_add: ∀ (v w : ℝ²), f_map (v + w) = f_map v + f_map w :=
begin
    -- Wähle zwei beliebige Vektoren mit `intros` aus.
    intros,
    -- Das Lemma `funext` sagt das zwei Funktionen identisch sind, wenn sie für jeden Wert ereinstimmen:
    -- `(∀ i, f i = g i) → f = g`. Da Vektoren einfach als Funktionen von einem Indexset codiert sind,
    -- kannst du mit `apply funext` komponentenweise rechnen.
    funext i,
    -- Mit `fin_cases i` kannst du pro möglichem Wert von `i` ein Goal auftun. D.h. im ersten gilt dann
    -- `i = 0`, im zweiten Goal `i = 1`.
    fin_cases i,

    {
      -- Dies ist der Fall `i = 0`.
      -- Um konkret zu rechnen, muss man manchmal Definitionen konkret anwenden. Dies geschieht mit
      -- `unfold f_map`.
      unfold f_map,
      -- Das Goal hat jetzt Terme der Form `![a, b] 0`, und du weisst was das sein sollte, nämlich
      -- einfach der erste Komponent `a`. Die Taktik `simp` ist für solche Vereinfachungnen gedacht. 
      simp,
      -- Einfache Rechenaufgaben hast du ja bereits gemacht.
      -- `ring` oder `linarith` machen dies automatisch für dich.
      ring,
    },
    {
      -- Und jetzt noch den Fall `i = 1`.
      unfold f_map,
      simp,
      ring,
    }
end
