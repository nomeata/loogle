#!/usr/bin/env bash

# Usage: $0 dest/
#
# This script
# * creates a temporary directory in dest/build/
# * fetches the latest loogle
# * runs lake update to get the latest mathlib
# * builds the loogle binary and the mathlib cache
# * does a quick sanity check
# * atomically replaces the dest/deploy/live symlink
# * if successful, delets all other directories

set -e

DEST="$1"
if [ -z "$DEST" ]; then
    echo "Usage $0 dest/"
    exit 1
fi

mkdir -p "$DEST/build" "$DEST/deploy"
cd "$DEST"

echo "Cleaning up $DEST/build"
cd build/
old_live="$(readlink ../deploy/live)"
echo "Currently live: $old_live"
for file in deploy-*; do
  if [ "../build/$file" != "$old_live" ] && [ "../build/$file" != "$old_live.log" ]; then
    echo "Deleting old build $file"
    rm -rf "$file"
  fi
done

workdir="deploy-$(date --iso=seconds)"
logfile="$workdir.log"
exec &> >(tee -a "$logfile")

echo "Working in $DEST/build/$workdir"
echo "Cloning loogle"
git clone --depth=1 https://github.com/nomeata/loogle.git "$workdir"
cd "$workdir"
git log -n 1

echo "Replace toolchain by mathlib's"
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
cat lean-toolchain
rm ./lake-manifest.json

echo "Updating lake"
export LOOGLE_SECCOMP=true
lake update
cat ./lake-manifest.json

echo "Fetching mathlib cache"
lake exe cache get

echo "Building loogle"
lake build loogle

echo "Building mathlib cache"
lake exec loogle --write-index ./.lake/build/lib/LoogleMathlibCache.extra

echo "Sanity checks"
echo "Does .extra exist?"
ls -sh ./.lake/build/lib/LoogleMathlibCache.extra
echo "Does the binary exist?"
test -x ./.lake/build/bin/loogle

echo "Does it run"
./.lake/build/bin/loogle

echo "Does it work (fast enough, so using the cache)"
timeout 30s ./.lake/build/bin/loogle List.replicate|grep -q 'List.replicate (from Init.Data.List.Basic)'

echo "Size of .lake"
ls -sh .lake

echo "All good, going live"
cd .. # in build/ now

rm -f tmp
ln -s "../build/$workdir" tmp
mv -T tmp ../deploy/live

for file in deploy-*; do
  if [ "$file" != "$workdir" ] && [ "$file" != "$logfile" ]; then
    echo "Deleting old build $file"
    rm -rf "$file"
  fi
done

echo "All done"
