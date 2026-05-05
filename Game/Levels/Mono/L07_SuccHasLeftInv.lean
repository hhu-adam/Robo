import Game.Levels.Mono.L06_StrictMono

World "Mono"
Level 7

Title ""

Introduction ""

open Function Nat

Statement : HasLeftInverse succ  := by
  /-
  Hint "**Du**: Behauptet wird offenbar, dass die Abbildung `n ↦ n + 1` ein Linksinverses besitzt.
  Ich gebe also einfach die Abbildung `n ↦ n - 1` an … außer, dass das für `n = 0` nicht funktioniert.

  **Robo**:  Du könntest ja mit `if … then … else` eine Fallunterscheidung machen.
  Aber tatsächlich brauchst du das gar nicht.  In Leansch liegt auch `0 - 1` in `ℕ`.

  **Du**: Was … ??!

  **Robo**:  Ja.  Das ist einfach wieder als `0` definiert.
  "
  -/
  Hint "It conjected that `n ↦ n + 1` has left inverse. One would assume that `n ↦ n - 1` would
  not work for `n = 0`. Tackling this by case distinction e.g. `if … then … else` is unecessary as
  in Leanic `0 - 1` is in `ℕ`. It is simply defined as `0`"
  Branch
    use (fun n ↦ if 0 < n then n - 1 else 0)
    /-
    Hint "**Robo**: Das sieht gut aus.  Aber glaub mir, die Verzweigung ist ganz unnötig.
    Du könntest auch einfach `n ↦ n - 1` verwenden.  Probiers mal!"
    -/
    Hint "[Hint wdpf] Try `n ↦ n - 1`"
  Branch
    use (fun n ↦ if 0 < n then n - 1 else 0)
    unfold LeftInverse
    /-
    Hint "**Robo**: Das sieht gut aus.  Aber glaub mir, die Verzweigung ist ganz unnötig.
    Du könntest auch einfach `n ↦ n - 1` verwenden.  Probiers mal!"
    -/
    Hint "[Hint wdpf] Try `n ↦ n - 1`"
  Branch
    let g := (fun n ↦ if 0 < n then n - 1 else 0)
    /-
    Hint "**Robo**: Das sieht gut aus.  Aber glaub mir, die Verzweigung ist ganz unnötig.
    Du könntest auch einfach `n ↦ n - 1` verwenden.  Probiers mal!"
    -/
    Hint "[Hint wdpf] Try `n ↦ n - 1`"
  use (fun n ↦ n - 1)
  true_simp? [LeftInverse]

/-
Conclusion "
  **Du**:  Ich bin immer noch schockiert.
  Ich dachte, wir machen hier Mathematik.
  Wieso sollte denn `0 - 1` wieder `0` sein??

  **Robo**:  Reine Ansichtssache.  Du stellst dir `n ↦ n - 1` vor als eine Abbildung, die nur auf den positive natürlichen Zahlen definiert ist.
  In Leansch ist `n ↦ n - 1` eben eine Abbildung, die auf allen natürlichen Zahlen definiert ist, und sie schickt `0` auf `0`.
  Warum nicht.  Anwenden wird man diese Abbildung am Ende eh nur auf positive Zahlen, und auf denen stimmt deine Interpretation ja glücklicherweise mit der leanschen Interpretation überein.
"
-/
Conclusion "Conclusion Mono L07: Explain that here `0 - 1` is `0`, as there is mapping `n ↦ n - 1` defined only on natural numbers.
In Lean `n ↦ n - 1` is such a mapping and there for it maps `0` onto `0`.
"
