#!/bin/bash

# cd "$(dirname $0)"

NEWSIZE="1000x1000^"

for filename in $(dirname $0)/FullSizeOriginals/*; do
  [ -e "$filename" ] || continue

  NEWFILE=$(dirname $0)/$(basename $filename)

  convert -resize $NEWSIZE $filename $NEWFILE

  echo "copying and reducing $filename to $NEWFILE."

done
