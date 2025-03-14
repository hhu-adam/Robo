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

## Refactoring existing worlds

The bash script `sofi.sh` (`s`ort `o`ut `f`ilnames and `i`mports), contained in the root folder,
can help restructure existing worlds, for example if you want to reorder or rename existing levels,
or add additional levels in the middle.  Say, for example, you have an “Arithmetic World” in the
folder

    Game/Levels/Arithmetic

consisting of the three levels listed in the leftmost column of the table below. Suppose you want to
switch the order of multiplication and addition, and insert an additional level on subtraction in
between.  Then you can simply edit the *file names* as in the second column, and add the additional
file for the level on substraction, so that the files are in the intended order when sorted
alphabetically (as displayed in the third column).

| existing levels    | manual changes           | files in alphabetical order | end result          |
|--------------------|--------------------------|-----------------------------|---------------------|
| L01\_hello.lean    | L01\_hello.lean          | L01\_hello.lean             | L01\_hello.lean     |
| L02\_multiply.lean | **L03**\_multiply.lean   | L02a\_add.lean              | L02\_add.lean       |
| L03\_add.lean      | **L02a**\_add.lean       | L02b\_substract.lean        | L03\_substract.lean |
|                    | **L02b\_substract.lean** | L03\_multiply.lean          | L04\_multiply.lean  |

Calling

    ./sofi.bash Game/Levels/Arithmetic

will then

- rename the files as in the last column,
- update the level number in each file,
- make a reasonable attempt to update the `import` statements in each of the
  level files, and
- update the imports in the base file `Game/Levels/Arithmetic.lean`.

More details are documented in the script itself.

Don't forget to add all your new/renamed files to git with

    git add Game/Levels/Arithmetic/

at the end.
