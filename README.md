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

Please prioritise translation of the following planets, as they are
essentially finalised:

* Logo
* Implis

For translation, we use [`lean-i18n`](https://github.com/hhu-adam/lean-i18n). In particular, you can (optionally) build the lean project `Robo` once to make sure the file `.i18n/de/Game.pot` is up-to-date,
then use any software to create a file `./i18n/en/Game.po` containing the translations (where you replace `en` with the ISO language code for your language). The recommended software for editing PO-files is [Poedit](https://poedit.net/)

## New Content

Contributions of new planets are welcome! Each planet in the game talks about a new topic
in a standard Mathematics undergrad (bachelor) curriculum at university.

Please follow our [Contribution Guide](./docs/NewPlanet.md) which helps you creating
new content step-by-step.

# Technical

## Building

You can build the game just like a regular Lean project. In particular, inside `Robo/` you should call

```
lake update -R
lake build
```

*Note: the repo is set up in a way that `lake update` is NOT destructive and can be called liberally anytime. (This is not true for other Lean projects)*

*Note: `lake update` will call the two commands `lake exe cache get` (retrieve the latest mathlib cache) and `lake build gameserver` (build the gameserver executable); so if you're not calling `lake update`, you should call these two commands manually.*

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
