#!/bin/bash

cd "$(dirname $0)"

# Delete all .png files in the current directory and its subdirectories
echo "deleting old reduced .png files"
find . -type f -name "*.png" -delete
rm -rf ./tmp-download

GIT_LFS_SKIP_SMUDGE=1 git clone --depth=1 --filter=blob:none https://github.com/joneugster/Robo-Images.git ./tmp-download

NEWSIZE="1000x1000^"

# Find all files recursively in the fullsize directory
find ./tmp-download/fullsize -type f | while read -r filename; do
  [ -e "$filename" ] || continue

  # Create the corresponding directory structure in the target location
  NEWFILE="$(dirname $0)/${filename#./tmp-download/fullsize/}"

  # Ensure the directory exists before converting
  mkdir -p "$(dirname "$NEWFILE")"

  # Convert and resize the image
  convert -thumbnail $NEWSIZE -define png:exclude-chunks=date -define png:include-chunk=none "$filename" "$NEWFILE"

  echo "Copying and reducing $filename to $NEWFILE."

done

echo "Deleting ./tmp-download."

rm -rf ./tmp-download
