#!/usr/bin/env bash

# Usage: $0 build/ dest-link cmd ...
#
# This script
# * deletes all entries in build not pointed to by dest-link
#   (to avoid the disk from filling up)
# * creates a fresh directory in build/
# * runs `cmd ...`  in this directory, keeping a logfile
# * if successful, atomically replaces the dest-link symlink to point to that directory

set -e
shopt -s nullglob

function usage () {
    echo "Usage $0 build/ dest-link cmd ..."
    exit 1
}

BUILD="$1"
[ -n "$BUILD" ] || usage
shift

DEST="$1"
[ -n "$DEST" ] || usage
shift

mkdir -p "$BUILD"
mkdir -p "$(dirname "$DEST")"

if [ -e "$DEST" ]
then
  echo "Cleaning up $BUILD"
  old_live="$(realpath $DEST)" # nb: no -s!
  echo "Currently live: $old_live"
  for file in "$BUILD"/deploy-*; do
    abs_file="$(realpath "$file")"
    if [ "$abs_file" != "$old_live" ] && [ "$abs_file" != "$old_live.log" ]; then
      echo "Deleting old build $file"
      rm -rf "$file"
    fi
  done
fi

workdir="deploy-$(date --iso=seconds)"
logfile="$BUILD/$workdir.log"
mkdir -p "$BUILD/$workdir"

( cd "$BUILD/$workdir"; "$@" ) &> >(tee -a "$logfile")

echo "Working in $BUILD/$workdir"

rel_path="$(realpath "$BUILD/$workdir" --relative-to="$(dirname "$DEST")")"
ln -s $rel_path $DEST.tmp.$workdir
mv -T $DEST.tmp.$workdir $DEST

echo "All done"
