import Game.Metadata

World "Implis"
Level 5

Title "" -- "Implikation"

/-
Introduction
"
Die nächste Seite sieht ein bisschen komplizierter aus. Damit Ihr nicht die Übersicht verliert, fasst Robo sofort die verschiedenen Implikationen in einem Diagramm zusammen.
  $$
  \\begin{CD}
       A  @>{f}>> B @<{g}<< C    \\\\ %(new line)
    @V{h}VV    @V{i}VV   @V{j}VV \\\\ %(new line)
       D  @<{k}<< E @>{l}>> F    \\\\ %(new line)
    @A{m}AA    @A{n}AA   @V{p}VV \\\\ %(new line)
       G  @<{q}<< H @>{r}>> I
  \\end{CD}
  $$
"
-/
Introduction "Intro Implis L05: Introduce implication graph
  $$
  \\begin{CD}
       A  @>{f}>> B @<{g}<< C    \\\\ %(new line)
    @V{h}VV    @V{i}VV   @V{j}VV \\\\ %(new line)
       D  @<{k}<< E @>{l}>> F    \\\\ %(new line)
    @A{m}AA    @A{n}AA   @V{p}VV \\\\ %(new line)
       G  @<{q}<< H @>{r}>> I
  \\end{CD}
  $$
  "

Statement
    (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F)
    (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  /-
  Hint "
    **Du**: Also ich muss einen Pfad von Implikationen $A \\Rightarrow I$ finden.

    **Robo**: Lass mich mal raten, wie wir anfangen … Wieder `intro`?"
  -/
  Hint "Find an implication path $A \\Rightarrow I$. Try `intro`"
  intro hyp
  -- Hint (hidden := true) "**Robo**: Na wieder `apply`, was sonst."
  Hint (hidden := true) "Hier again use `apply`"
  Branch
    apply r
    -- Hint "**Robo**: Das sieht nach einer Sackgasse aus …"
    Hint "Story"
  Branch
    apply p
    Branch
      apply j
      -- Hint "**Robo**: Das sieht nicht gut aus."
      Hint "Story"
    apply l
    Branch
      apply n
      -- Hint "**Robo**: Nah, da stimmt doch was nicht …"
      Hint "Story"
    apply i
    Branch
      apply g
      -- Hint "**Robo**: Halt! Falsch abgebogen."
      Hint "Story"
    apply f
    assumption
  Branch
    apply h at hyp
    -- Hint "**Robo**: Bist du dir sicher?"
    Hint "Story"
  apply f at hyp
  apply i at hyp
  Branch
    apply k at hyp
    -- Hint "**Robo**: Ehm …"
    Hint "Story"
  apply l at hyp
  apply p at hyp
  assumption

/-
Conclusion
"
Der Operationsleiter bedankt sich wieder artig. Er drückt wieder auf ein paar Knöpfe,
und mit einem lauten Ratteln springen mehrere Förderbänder gleichzeitig wieder an.
"
-/
Conclusion "Conclusion Implis L05"

DisabledTactic tauto
