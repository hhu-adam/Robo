import Game.Metadata

World "Uncountable"
Level 8

universe u

open Module Cardinal

Statement {α β : Type u} : #α ^ #β = #(β → α) := by
  apply Cardinal.power_def

/---/
TheoremDoc Cardinal.power_def as "Cardinal.power_def" in "Cardinal"

NewTheorem Cardinal.power_def
