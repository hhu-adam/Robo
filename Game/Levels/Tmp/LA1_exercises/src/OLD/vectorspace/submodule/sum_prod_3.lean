-- Level name : Externes Produkt

-- begin hide
import vectorspace.submodule.sum_prod_2
import data.real.basic            -- definiert `ℝ`
import algebra.module.pi          -- definiert `module ℚ (fin 2 → ℚ)`
-- end hide

import data.real.basic            -- definiert `ℝ`
import algebra.module.pi
import algebra.module.prod
import algebra.module.submodule.basic
import algebra.algebra.bilinear

import linear_algebra.basic
import linear_algebra.span
import linear_algebra.prod
import data.dfinsupp.basic

notation `ℝ²` := fin 2 → ℝ

/-
Die externe Summe von (Unter-) Modulen wird als `V × W` geschrieben 
Das Produkt zweier Module wird mit `×` geschrieben.

Lean weiss dann automatisch, dass das Produkt wieder ein Vektorraum ist.
-/
example : module ℝ (ℝ × ℝ) := infer_instance

/-
Und `ℝ × ℝ` und `fin 2 → ℝ` sind natürlich Isomorph. In Praxis eignet sich
die Funktionsschreibweise besser, deshalb verwenden wir diese als
definition für `ℝ²`.

Hier die Äquivalenz als generelle Typen:
-/
example : (fin 2 → ℝ) ≃ ℝ × ℝ  :=
begin
  apply pi_fin_two_equiv,
end

/-
Äquivalenz als Vektorräume schreibt man als `ℝ`-lineare Äquivalenz `≃ₗ[ℝ]`.
-/

/- Lemma
Zeige dass das Produkt `ℝ × ℝ` und `ℝ²` isomorph sind als `ℝ`-Vektorräume.
-/
example : ((fin 2) → ℝ) ≃ₗ[ℝ] ℝ × ℝ  :=
begin
  sorry
end