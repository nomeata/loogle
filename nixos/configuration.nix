{ config, self, inputs, pkgs, modulesPath, lib, environment, loogle_server, nixpkgs, ... }:
{
  imports = [ (modulesPath + "/profiles/qemu-guest.nix") ];

  # for testing
  # virtualisation.forwardPorts = [
  #   { from = "host"; host.port = 8888; guest.port = 80; }
  # ];
  # virtualisation.memorySize = 2048;
  # users.users.root.initialPassword = "test";

  boot.loader.grub.device = "/dev/sda";
  boot.initrd.availableKernelModules = [ "ata_piix" "uhci_hcd" "xen_blkfront" "vmw_pvscsi" ];
  boot.initrd.kernelModules = [ "nvme" ];
  fileSystems."/" = { device = "/dev/sda1"; fsType = "ext4"; };

  boot.tmp.cleanOnBoot = true;
  zramSwap.enable = true;
  networking.hostName = "loogle";

  users.users.root.openssh.authorizedKeys.keys = [
    "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIJRd0CZZQXyKTEQSEtrIpcTg15XEoRjuYodwo0nr5hNj jojo@kirk"
    "ecdsa-sha2-nistp256 AAAAE2VjZHNhLXNoYTItbmlzdHAyNTYAAAAIbmlzdHAyNTYAAABBBMYx13rpT1E87lw5yNyRs1Lq3/vwd3fxjRwq9nJz4b3iVSAGXnwUxDVbi3m2H1NSNCsoOFOVej+yPMkmIs/+Wxo= pixel-tpm"
  ];

  nix.settings.substituters = [
    "https://cache.nixos.org/"
    "https://cache.garnix.io"
  ];
  nix.settings.trusted-public-keys = [
    "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
    "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g="
  ];

  # enable nix flakes
  nix.settings.experimental-features = ["nix-command" "flakes"];
  nix.registry.nixpkgs.flake = nixpkgs;
  nix.nixPath = [
    "nixpkgs=/etc/nixpkgs/channels/nixpkgs}"
    "/nix/var/nix/profiles/per-user/root/channels"
  ];
  systemd.tmpfiles.rules = [
    "L+ /etc/nixpkgs/channels/nixpkgs     - - - - ${nixpkgs}"
  ];


  documentation.nixos.enable = false;
  documentation.enable = false;

  security.acme.defaults.email = "mail@joachim-breitner.de";
  security.acme.acceptTerms = true;

  services.openssh = {
    enable = true;
    ports = [ 2722 ];
    settings.PasswordAuthentication = false;
  };


  services.nginx = {
    enable = true;
    enableReload = true;
    recommendedProxySettings = true;
    recommendedGzipSettings = true;
    recommendedOptimisation = true;
    recommendedTlsSettings = true;
    proxyTimeout = "300s";
  };

  services.nginx.virtualHosts = {
    "loogle.lean-lang.org" = {
      enableACME = true;
      forceSSL = true;
      locations = {
        "/" = {
          proxyPass = "http://localhost:8080";
        };
      };
    };
    "loogle.lean-fro.org" = {
      enableACME = true;
      forceSSL = true;
      globalRedirect = "loogle.lean-lang.org";
    };
    "loogle.nomeata.de" = {
      enableACME = true;
      forceSSL = true;
      globalRedirect = "loogle.lean-lang.org";
    };
  };

  users.users.loogle = {
    isNormalUser = true;
  };

  systemd.services.loogle = {
    description = "Loogle";
    enable = true;
    after = [
      "network.target"
    ];
    wantedBy = [
      "multi-user.target"
    ];
    serviceConfig = {
      Type = "simple";
      User = "loogle";
      Restart = "always";
      WorkingDirectory = "${loogle_server}";
      ExecStart = "${loogle_server}/bin/loogle_server";
      NoNewPrivileges = true;
      ProtectSystem = "strict";
      ProtectHome = "read-only";
      Environment = "LOOGLE_REV=${self.rev or "dirty"} MATHLIB_REV=${inputs.mathlib4.rev or "dirty"}";
    };
  };

  swapDevices = [{ device = "/swapfile"; size = 2048; }];

  nix.settings.sandbox = false;

  # Automatic garbage collection. Enabling this frees up space by removing unused builds periodically
  nix.gc = {
    automatic = false;
    dates = "weekly";
    options = "--delete-older-than 30d";
  };

  networking.firewall.enable = true;
  networking.firewall.allowedTCPPorts = [ 80 443 22 ];

  services.journald.extraConfig = "SystemMaxUse=100M";

  programs.vim.defaultEditor = true;

  services.fail2ban.enable = true;
  system.stateVersion = "22.11";
}
