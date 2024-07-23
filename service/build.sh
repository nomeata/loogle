#!/usr/bin/env bash

set -e

echo "Cloning loogle"
git clone --depth=1 https://github.com/nomeata/loogle.git .
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

echo "Does it work"
./.lake/build/bin/loogle List.replicate|grep -q 'List.replicate (from Init.Data.List.Basic)'

# Disabled for now, until moved to a faster server
# echo "Does it work (fast enough, so using the cache)"
# timeout 15s ./.lake/build/bin/loogle List.replicate|grep -q 'List.replicate (from Init.Data.List.Basic)'

echo "Size of .lake"
ls -sh .lake

echo "All good, ready to go"
