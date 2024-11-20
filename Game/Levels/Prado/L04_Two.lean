import Game.Metadata
import Game.Levels.Prado.L03_Prime

namespace Nat

World "Prado"
Level 4

Title "Zwei"

Introduction
"
"

Statement prime_two : Nat.Prime 2 := by
  Hint "**Du**: Also soll ich hier auch wieder `prime_def` verwenden?

  **Robo**: Könntest du, auch wenn das etwas mühsam werden kann. Viel einfacher: Mit konkreten
  Zahlen kannst du auch hier wieder `decide` verwenden!"
  decide

TheoremTab "Nat"
