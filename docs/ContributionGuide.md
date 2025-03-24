## Creating new content

This guide walks you through our preferred contribution process.

Please try to stick to the **three PR process** described below. It helps avoiding that you
do a lot of work that needs to be refactored/redone later!

## 0. Create a "Boss Level"

First, find an interesting target excercise for your topic of interest
(referred to as "Boss Level" here). Ideally it is an exercise which could also
be found on an excersise sheet in class, and ideally it is something that does not
exists as theorem in mathlib (although this is optional).

## 1. PR proof-of-concept

Proof this exercise in Lean, PR your suggestion to

```
Robo/Game/Levels/NewStuff/{MyNewExercise}.lean
```

and **ask for feedback** from us!

(note: the proof does not have to be curated at this step, but it helps demonstrating
which parts of the proof you intend to separate into their own levels)

## (1b.) Adding missing Tactics/Theorems

Meanwhile, to test your planet you can add

```
World "MyNewWorld"
Level 1
```

to the top of your file, replace the main `theorem`/`example` with `Statement`
and import your file in `Game.lean` with

```
import Game.Levels.NewStuff.MyNewExercise
```

If you run `lake build`, the game will show you some warnings about tactics/theorems which
are used but not yet implemented in the game.

* You can see these warnings in the command line or by setting
your cursor at `MakeGame` in the file `Game.lean`
* At this stage you should also be able to [start the game locally](https://github.com/leanprover-community/lean4game/blob/main/doc/running_locally.md) and see your planet and it's
  single level appearing in the game.

If your planet is planing to introduce these items, you can add them with the following commands
at the bottom of `Robo/Game/Levels/NewStuff/{MyNewExercise}.lean`:

```
NewTactic tactic₁ tactic₂
NewTheorem Nat.used_theorem₁ Function.Surjective.used_theorem₂
```

If the missing items don't conceptually belong into your planet you **should start a discussion**:

* maybe they can be added to an existing planet (e.g. a missing theorem about sums might fit well into "Babylon")
* or maybe they are missing because the game authors decided on an equivalent "canoncial way".
  (e.g. so far we did not ever use `exact`, but used `assumption` instead)


## 2. Level creation

If you receive positive feedback, it's time to split your proof into a series of levels
leading up to your Boss Level.

You may already add temporary hints inside your proof at this stage in places where the user needs
explanation/help, but don't bother writing them nicely!

Add the levels to single files
`Robo/Game/Levels/NewStuff/{MyNewExercise}/L{no}_{Keyword}.lean` and import these in `{MyNewExercise}.lean`.

Consult the [Lean4game documentation](https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md#3-creating-a-level) about level creation.

Once you're done, **PR the new planet** with all it's levels.

## 3. Story writing

Once the level structure stands and has been approved, it is time to add `Hints`,
a story to your Level, and the documentation of introduced Tactics/Theorems/Definitions.

Refer to the [Style Guide](./StyleGuide.md) where we started keeping track on uniform
style throughout the game.

*Note: This is the only step which is required to happen in German. We're also happy if you
just provide the content up to this step and leave this final step for a German speaking person.*
