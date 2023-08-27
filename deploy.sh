#!/usr/bin/env bash

set -e

nixos-rebuild switch --use-substitutes --target-host root@loogle.nomeata.de  --flake .#loogle --fast
ssh root@loogle.nomeata.de profile wipe-history --profile /nix/var/nix/profiles/system
ssh root@loogle.nomeata.de nix store gc
