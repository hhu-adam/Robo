import Game.Levels.Tmp.NullstellenSatz

-- By Michel & Julia

World "Tmp"
Level 2

Title "Zwischenwertsatz"

Introduction
""
open Set

/--
 -/
Statement (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (f_cont : ContinuousOn f (Icc a b))
    (f_retract : f '' (Icc a b) ⊂ Icc a b) : ∃ x ∈ (Icc a b), f x = x := by
  --unfold ContinuousOn at f_cont


-- --Zunächst benötigen wir eine Hilfsfunktion g:

  let g := fun (x : ℝ) ↦ x - f x

-- --Für diese wollen wir zeigen, dass sie stetig ist:

  have g_cont : ContinuousOn g (Icc a b)

  · apply ContinuousOn.sub          --g ist eine Differenz zweier Funktionen.
    apply continuousOn_id           --x ist als Funktion stetig.
    apply f_cont                         --f ist per Vorraussetzung stetig.
    --Folglich ist g stetig als Differenz zweier stetiger Funktionen

-- --Nun wollen wir zeigen, dass 0 im Intervall [ g(a) , g(b) ] enthalten ist:

  have nl: ((0 : ℝ) ∈ (Icc (g a) (g b)))
  · rw[mem_Icc]               --Dafür schreiben wir das Intervall um
    constructor                      --und teilen die Aussage in zwei Teile, die wir zeigen wollen.

    --Zuerst: g(a) ≤ 0
    · simp                       --Setzen g ein und vereinfachen das zu Zeigende.
      --Die gewünschte Aussage steht im Grunde in unser Annahme h2,
      --weswegen wir diese geeignet umschreiben und für unseren Fall spezialisieren.
      rw [ssubset_def] at f_retract
      rcases f_retract
      rw [subset_def] at left
      specialize left (f a)
      simp? at left
      specialize left (a)
      aesop

      --Dann: 0 ≤ g(b)
      --Das Vorgehen ist analog zum obigen Fall.
    · simp
      rw [ssubset_def] at f_retract
      rcases f_retract
      rw [subset_def] at left
      specialize left (f b)
      simp? at left
      specialize left (b)
      aesop

--Dann wollen wir zeigen, dass es ein x in [a , b] gibt mit g(x) = 0.
--Hierfür verwenden wir das oben gezeigte Lemma Nullstelle.
--Dieses wendet den Zwischenwertsatz an, den wir verwenden können, da g stetig ist.



  have t: ∃ x ∈ Icc a b, g x = 0
  · exact nullstellen_satz hab g_cont nl

--Jetzt ist der Beweis nicht mehr schwer, denn g(x) = 0 ist äquivalent zu f(x) = x.
--Wir wollen also unsere Annahme t so geeignet umschreiben, dass wir das zu zeigende dort stehen haben.

  simp only [g] at t         --Dafür setzen wir g in t ein.
  rcases t with ⟨x, hx, hx2⟩   --Dann teilen wir t auf in mehrere Aussagen.
  use x                       --Unser durch t gefundenes x wollen wir für unseren Beweis nutzen.
  --Jetzt muss gezeigt werden, dass x im gewünschten Intervall ist und die gewünschte Eigenschaft erfüllt.
  constructor
  assumption                --Das es im Intervall liegt, ist eine Annahme (hx).
  --Jetzt müssen wir nur noch durch Umformung hx2 da stehen haben und sind fertig.
  refine Eq.symm ?_
  refine sub_eq_zero.mp ?_
  assumption
-- end


Conclusion
""
