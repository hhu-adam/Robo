#!/bin/bash

cd "$(dirname $0)"

git clone https://github.com/joneugster/Robo-Images.git ./tmp-download

NEWSIZE="1000x1000^"

for filename in ./tmp-download/fullsize/*; do
  [ -e "$filename" ] || continue

  NEWFILE=$(dirname $0)/$(basename $filename)

  convert -thumbnail $NEWSIZE -define png:exclude-chunks=date -define png:include-chunk=none $filename $NEWFILE

  echo "Copying and reducing $filename to $NEWFILE."

done

echo "Deleting ./tmp-download."

rm -rf ./tmp-download
