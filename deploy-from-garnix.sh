#!/usr/bin/env bash

set -e

path="$(nix derivation show .#nixosConfigurations.loogle.config.system.build.toplevel | jq -r '.[].outputs.out.path')"
echo "Output path: $path"

echo "Checking if it is avaliable on garnix"
curl -o /dev/null -s --head --fail "https://cache.garnix.io/$(echo "$path" | cut -c12-43).narinfo"

echo "Yes it is, deploying..."

ssh root@loogle.nomeata.de nix-env -p /nix/var/nix/profiles/system --set "$path" --narinfo-cache-negative-ttl 0
ssh root@loogle.nomeata.de "$path"/bin/switch-to-configuration switch
ssh root@loogle.nomeata.de nix profile wipe-history --profile /nix/var/nix/profiles/system
ssh root@loogle.nomeata.de nix store gc
