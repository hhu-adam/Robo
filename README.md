# Robo

A game for learning Lean 4 in which a cute little smart-elf named Robo joins you on your exploration of a universe inhabited by formalosophers.

The game is currently available only in German.  It can be played at the [Lean Game Server](https://adam.math.hhu.de/).

## Overview over existing content

| Planet     | key mathematical content           | Lean tactics introduced               | Boss level                                                         |
|:---------- |:---------------------------------- | ------------------------------------- | ------------------------------------------------------------------ |
| Logo       | propositional logic: ∧, ∨, ¬       | `rfl`, `left`, `right`,`tauto`, …     | –                                                                  |
| Implis     | propositional logic: ⇒, ⇔          | `apply`, `intro`, `revert`, `rw`, …   | A ⇒ B equivalent to ¬ A ∨ B                                        |
| Saturn     | elementary arithmetic, polynomials | `ring`, `rw` for equations            | a well-known polynomial sums-of-squares formula                    |
| Quantus    | predicate logic, even/odd numbers  | `use`, `obtain`, `decide`, `push_neg` | [Drinker's paradox](https://en.wikipedia.org/wiki/Drinker_paradox) |
| Luna       | inequalities                       | `linarith`, `omega`                   | –                                                                  |
| Spinoza    | proof structuring                  | `suffices`, `by_contra`, `contrapose` | –                                                                  |
| Babylon    | ∑ notation, induction              | `induction'`                          | sum of cubes                                                       |
| Piazza     | basic set theory                   | `ext`, `simp`                         | –                                                                  |
| Prado      | prime numbers                      | –                                     | exactly one even prime                                             |
| Euklid     | ∏ notation                         | –                                     | infinitely many primes                                             |
| Vieta      | maps (between types)               | `funext`                              | another induction exercise                                         |
| Epo        | surjective maps, axiom of choice   | `choose`                              | map surjective ⇔ has right inverse                                 |
| Mono       | injective maps                     | –                                     | map injective ⇔ has left inverse                                   |
| Iso        | bijective maps                     | –                                     | map bijective ⇔ has inverse                                        |
| Samarkand  | (pre)images of subsets             | –                                     | map surjective ⇔ induced contravariant map on powersets injective  |
| Cantor     | fixed points of maps               | –                                     | ℕ-valued sequences uncountable                                     |
| Robotswana | matrices, trace                    | –                                     | characterization of trace map                                      |
| Ciao       | (good-bye planet)                  | –                                     | –                                                                  |


# Contribution

## Bugs

For small content fixes like spelling mistakes, missing hints, missing documentation, or other things that were unclear or you've struggled with, please open an Issue
or PR here!

Issues concerning the underlying software are better placed
in the [lean4game repo](https://github.com/leanprover-community/lean4game).

## New Content

Contributions of new planets are welcome! Each planet in the game talks about a new topic
in a standard Mathematics undergrad (bachelor) curriculum at university.

Please follow our [Contribution Guide](./docs/ContributionGuide.md),
 which helps you create new content step-by-step.

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
