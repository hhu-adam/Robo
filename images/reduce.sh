#!/bin/bash

cd "$(dirname $0)"

NEWSIZE="800^x800"

for filename in FullSizeOriginals/*; do
  [ -e "$filename" ] || continue

  NEWFILE=$(basename $filename)

  convert -resize $NEWSIZE $filename "$(dirname $0)/$NEWFILE"

  echo "copying and reducing $filename to $NEWFILE."

done
