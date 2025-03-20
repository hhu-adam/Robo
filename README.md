# Robo

A game for learning lean 4 where a cute little Robo joins you on your exploration through the universe inhabited by formalosophers.

The game is primarily in German and can be played at the [Lean Game Server](https://adam.math.hhu.de/).

# Contribution

## Bugs

For small content fixes like spelling mistakes, missing hints, missing documentation, or other things that were unclear or you've struggled with, please open an Issue
or PR here!

Issues concerning the underlying software are better placed
in the [lean4game repo](https://github.com/leanprover-community/lean4game).

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
can help restructure existing worlds, see the
 [documentation](https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md#5-refactoring-an-existing-world).
