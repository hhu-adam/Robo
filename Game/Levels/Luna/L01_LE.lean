import Game.Metadata

World "Inequality"
Level 1

Title "Kleinergleich"

Introduction
"
Du fühlst dich ein wenig überfahren, aber versuchst trotzdem, ein Gespräch zu beginnen.

**Du**: Ist gut, wir bemühen uns, nichts durcheinander zu bringen. Ist es sehr schwer,
hier Ordnung zu halten.

**Lina**: Nun, man muss schon das ein oder andere wissen … Zum Glück hilft mir Ritha.
Wenn Du mal probieren willst … hier ist mir gestern etwas verrutscht.
"

Statement
  (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
  Hint "
    **Robo**: Denk lieber nicht zu lange darüber nach. Das ist eine Kuriosität,
    dass `m < n` auf `ℕ` per Definition als `m + 1 ≤ n` definiert ist!

    **Lina**: Du verdirbst den Witz! Ich wollte ihn doch nur testen."
  rfl

OnlyTactic rfl

Conclusion "**Du**: Ha, ha … Und was muss man noch wissen?"
