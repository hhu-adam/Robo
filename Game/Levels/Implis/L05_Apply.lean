import Game.Metadata

World "Implication"
Level 5

Title "Implikation"

Introduction
"
Die nächste Seite sieht ein bisschen komplizierter aus. Damit Ihr nicht die Übersicht verliert, fasst Robo sofort die verschiedenen Implikationen in einem Diagramm zusammen.
  $$
  \\begin{CD}
       A  @>{f}>> B @<{g}<< C    \\\\
    @V{h}VV    @V{i}VV   @V{j}VV \\\\
       D  @<{k}<< E @>{l}>> F    \\\\
    @A{m}AA    @A{n}AA   @V{p}VV \\\\
       G  @<{q}<< H @>{r}>> I
  \\end{CD}
  $$
"
Statement
    (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F)
    (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  Hint "
    **Du**: Also ich muss einen Pfad von Implikationen $A \\Rightarrow I$ finden.

    **Robo**: Lass mich mal raten, wie wir anfangen … Wieder `intro`?"

  intro hyp
  Hint (hidden := true) "**Robo**: Na wieder `apply`, was sonst."
  Branch
    apply r
    Hint "**Robo**: Das sieht nach einer Sackgasse aus …"
  Branch
    apply p
    Branch
      apply j
      Hint "**Robo**: Das sieht nicht gut aus."
    apply l
    Branch
      apply n
      Hint "**Robo**: Nah, da stimmt doch was nicht …"
    apply i
    Branch
      apply g
      Hint "**Robo**: Halt! Falsch abgebogen."
    apply f
    assumption
  Branch
    apply h at hyp
    Hint "**Robo**: Bist du dir sicher?"
  apply f at hyp
  apply i at hyp
  Branch
    apply k at hyp
    Hint "**Robo**: Ehm …"
  apply l at hyp
  apply p at hyp
  assumption

Conclusion
"
Der Operationsleiter bedankt sich wieder artig. Er drückt wieder auf ein paar Knöpfe,
und mit einem lauten Ratteln springen mehrere Förderbänder gleichzeitig wieder an.
"

DisabledTactic tauto
