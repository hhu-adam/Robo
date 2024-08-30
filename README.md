# Robo

A game for learning lean 4 where a cute little Robo joins you on your exploration through the universe inhabited by formalosophers.

The game is primarily in German and can be played at the [Lean Game Server](https://adam.math.hhu.de/).

# Contribution

## Bugs

For small content fixes like spelling mistakes, missing hints, missing documentation, or other things that were unclear or you've struggled with, please open an Issue
or PR here!

Issues concerning the underlying software are better placed
in the [lean4game repo](https://github.com/leanprover-community/lean4game).

## Translation

Translations of the content from German into other languages are very welcome, but please not that a large part of the game isn't finalised yet.

Please preoritiise translation of the following planets, as they are
essentially finalised:

* Logos
* Implis

For translation, we use [`lean-i18n`](https://github.com/hhu-adam/lean-i18n). In particular, you can (optionally) build the lean project `Robo` once to make sure the file `.i18n/de/Game.pot` is up-to-date,
then use any software to create a file `./i18n/en/Game.po` containing the translations (where you replace `en` with the ISO language code for your language). The recommended software for editing PO-files is [Poedit](https://poedit.net/)

## New Content

Contributions of new planets are welcome! Each planet in the game talks about a new topic
in a standard Mathematics undergrad (bachelor) curriculum at university.

1. First, find an interesting target excercise for your topic of interest
   (referred to as "Boss Level" here). Ideally it is an exercise which could also
   be found on an excersise sheet in class, and ideally it is something that does not
   exists as theorem in mathlib (although this is optional).
1. Proof this exercise in Lean, PR your suggestion to
   `Robo/Game/Levels/NewStuff/{MyNewExercise}.lean`, and
   ask for feedback from us!
   (note: the proof does not have to be curated at this step, but it helps demonstrating
   which parts of the proof you intend to separate into their own levels)
1. If you receive positive feedback, it's time to split your proof into a series of levels
   leading up to your Boss Level. You can PR them to single files `Robo/Game/Levels/NewStuff/{MyNewExercise}/L{no}_{Keyword}.lean` and import these in `{MyNewExercise}.lean`.
   Consult the [Lean4game documentation](https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md#3-creating-a-level)
   about level creation.
1. Once the level structure stands and has been reviewed, it is time to add `Hints` and
   a story to your Level

See also the [Style Guide](./STYLEGUIDE.md) where we started keeping track on uniform
style throughout the game.

# Techincal

## Building

You can build the game just like a regular Lean project. In particular, inside `Robo/` you should call

```
lake update -R
lake build
```

*Note: the repo is set up in a way that `lake update` is NOT destructive and can be called liberally anytime. (This is not true for other Lean projects)*

## Updating Lean/Mathlib

In order to update the Lean version used by the game, you should follow these steps:

* See what versions are available of `lean4game`: [Releases](https://github.com/leanprover-community/lean4game/releases)
* Modify the file `lean-toolchain` to contain the string `leanprover/lean4:v4.7.0` where `v4.7.0` is replaced by the newest version available.
* Call `lake update -R` and `lake build`. Your game now uses the specified Lean version and the corresponding mathlib release.

## Renaming levels

If you rename Levels under `Game/Levels/{MyPlanet}/_.lean` you can automatically update the planet file `Game/Levels/{MyPlanet}.lean`:

(all bash commands are from the cwd `Robo/`)

* Rename the level files in `Game/Levels/{MyPlanet}/` to your liking. Ideally they have the
  form `L02_ShortKeyword.lean` where the number `02` matches what's set inside the game.
* Use `git add Game/Levels/{MyPlanet}/` to stage all your changed files for commit.
* Once staged, run `./mk_all.sh`. This should update the imports in the planet file
  `Game/Levels/{MyPlanet}.lean` to match the folder's content.
* `git add Game/Levels/{MyPlanet}.lean`, then commit your renaming changes.
