#! /usr/bin/env bash
cd "$(git rev-parse --show-toplevel)" || exit 1

for planet in Game/Levels/*/; do
  FILE="$(dirname $planet)/$(basename $planet).lean"
  sed -i '/^import /d' "$FILE"

  #sed -i '1i import Bugs\nimport More' "$(dirname $planet)/$(basename $planet).lean"

  NEW=`git ls-files "$planet/*.lean" | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /'`

  # echo "\n\n\n"
  echo $NEW

  echo -e "$NEW\n$(cat $FILE)" > $FILE
done

#git ls-files "Game/Levels/*/" | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /'  > "Game.lean"


# for gp in Mathlib MathlibExtras Mathlib/Tactic Counterexamples Archive
# do
#   git ls-files "$gp/*.lean" | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$gp.lean"
# done
