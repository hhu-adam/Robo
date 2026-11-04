#!/usr/bin/env bash
# Give every module in this Lake project's build directories an empty .ilean,
# so the Lean language server's watchdog loads no reference data (it silently
# skips .ilean files it cannot parse), while Lake still sees all build outputs
# as present.
#
# Usage: ./stub-ileans-empty.sh   (run from anywhere; acts on the folder this script is in)
#
# Files are written to a temporary name and then moved into place, so that a
# .ilean hard-linked into Lake's shared cache is replaced, not overwritten.

set -euo pipefail

cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
[ -d .lake ] || { echo "no .lake directory in $PWD" >&2; exit 1; }

count=0
while IFS= read -r -d '' olean; do
  ilean=${olean%.olean}.ilean
  : > "$ilean.tmp"
  mv "$ilean.tmp" "$ilean"
  count=$((count + 1))
done < <(find .lake -name '*.olean' -print0)

echo "wrote $count empty .ilean files"
