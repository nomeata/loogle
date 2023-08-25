#!/usr/bin/env bash

nixos-rebuild switch --use-substitutes --target-host root@loogle.nomeata.de  --flake .#loogle --fast
