import data.set.intervals.basic
import data.real.basic
import topology.basic
import data.set.image
import topology.continuous_function.algebra
import algebra.support
import topology.instances.real
import topology.algebra.order.intermediate_value

-- Sei I = [a, b] und f : I → R stetig mit f(I) ⊂ I. 
-- Zeige, dass es ein x ∈ I gibt, so dass f(x) = x.

--------------------------------------------------

-- Wir benötigen, das folgende Lemma Nullstellen, welches den Zwischenwertsatz für uns anwendet:

lemma nullstelle {a b : ℝ} (j: a ≤ b) {g : ℝ  → ℝ}
  (h0: continuous_on g (set.Icc a b)) (l: (0 : ℝ) ∈ set.Icc (g a) (g b)) :
  ∃ (x : ℝ) (H : x ∈ set.Icc a b), g x = 0 :=
begin
  have h₁ := intermediate_value_Icc j h0,
  library_search,
end

-------------------------------------------------

example (a b: ℝ) (h3: a ≤ b ) (f : ℝ → ℝ ) 
[h1: continuous_on f (set.Icc a b)] [h2: set.image f (set.Icc a b) ⊂ set.Icc a b]: 
∃ (x ∈ (set.Icc a b)), f x = x :=

begin

  rw[continuous_on] at h1,

--Zunächst benötigen wir eine Hilfsfunktion g:

  let g := λ (x : ℝ ), x - f x,

--Für diese wollen wir zeigen, dass sie stetig ist:

have cg : continuous_on g (set.Icc a b),
    apply continuous_on.sub,          --g ist eine Differenz zweier Funktionen.
    apply continuous_on_id,           --x ist als Funktion stetig.
    apply h1,                         --f ist per Vorraussetzung stetig.
  --Folglich ist g stetig als Differenz zweier stetiger Funktionen

--Nun wollen wir zeigen, dass 0 im Intervall [ g(a) , g(b) ] enthalten ist:

  have nl: ((0 : ℝ ) ∈ (set.Icc (g a) (g b))),
    rw[set.mem_Icc],                  --Dafür schreiben wir das Intervall um
    constructor,                      --und teilen die Aussage in zwei Teile, die wir zeigen wollen.
    
    --Zuerst: g(a) ≤ 0
    simp,                             --Setzen g ein und vereinfachen das zu Zeigende.
    --Die gewünschte Aussage steht im Grunde in unser Annahme h2, 
    --weswegen wir diese geeignet umschreiben und für unseren Fall spezialisieren.
    rw [set.ssubset_def] at h2, 
    rcases h2,
    rw [set.subset_def] at h2_left,
    specialize h2_left (f a),
    simp? at h2_left, 
    specialize h2_left (a),
    tauto,

    --Dann: 0 ≤ g(b)
    --Das Vorgehen ist analog zum obigen Fall.
    simp,
    rw [set.ssubset_def] at h2,
    rcases h2,
    rw [set.subset_def] at h2_left,
    specialize h2_left (f b),
    simp? at h2_left,
    specialize h2_left (b),
    tauto,

--Dann wollen wir zeigen, dass es ein x in [a , b] gibt mit g(x) = 0.
--Hierfür verwenden wir das oben gezeigte Lemma Nullstelle.
--Dieses wendet den Zwischenwertsatz an, den wir verwenden können, da g stetig ist.

  have t: ∃ x ∈ set.Icc a b, g x = 0,
    apply nullstelle h3 cg nl,

--Jetzt ist der Beweis nicht mehr schwer, denn g(x) = 0 ist äquivalent zu f(x) = x.
--Wir wollen also unsere Annahme t so geeignet umschreiben, dass wir das zu zeigende dort stehen haben.

  simp only [g] at t,          --Dafür setzen wir g in t ein.
  rcases t with ⟨x, hx, hx2⟩,   --Dann teilen wir t auf in mehrere Aussagen.
  use x,                       --Unser durch t gefundenes x wollen wir für unseren Beweis nutzen.
  --Jetzt muss gezeigt werden, dass x im gewünschten Intervall ist und die gewünschte Eigenschaft erfüllt.
  constructor,
  assumption,                  --Das es im Intervall liegt, ist eine Annahme (hx).
  --Jetzt müssen wir nur noch durch Umformung hx2 da stehen haben und sind fertig.
  refine eq.symm _,
  refine sub_eq_zero.mp _,
  assumption,
end

