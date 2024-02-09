{ config, self, pkgs, modulesPath, lib, environment, nixpkgs, ... }:
let
  # a bit of a hack
  inVM = config.networking.dhcpcd.extraConfig == "noarp";
in {
  imports = [ (modulesPath + "/profiles/qemu-guest.nix") ];

  # for testing with
  # nix run .#nixosConfigurations.loogle.config.system.build.vm
  virtualisation.vmVariant = {
    virtualisation.forwardPorts = [
      { from = "host"; host.port = 8888; guest.port = 80; }
    ];
    virtualisation.memorySize = 8096;
    virtualisation.diskSize = 50000;
    users.users.root.initialPassword = "test";
  };

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
    "nixpkgs=/etc/nixpkgs/channels/nixpkgs"
    "/nix/var/nix/profiles/per-user/root/channels"
  ];
  systemd.tmpfiles.rules = [
    "L+ /etc/nixpkgs/channels/nixpkgs     - - - - ${nixpkgs}"
  ];

  documentation.nixos.enable = false;
  documentation.enable = false;

  environment.systemPackages = [
    pkgs.lsof
    self.packages.${pkgs.system}.loogle-updater
  ];

  security.acme.defaults.email = "mail@joachim-breitner.de";
  security.acme.acceptTerms = true;

  services.openssh = {
    enable = true;
    ports = [ 22 ];
    settings.PasswordAuthentication = false;
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
    path = [
      (pkgs.python3.withPackages(p: with p; [prometheus-client]))
      pkgs.gitMinimal
    ];
    serviceConfig = {
      Type = "simple";
      User = "loogle";
      Restart = "always";
      WorkingDirectory = "/home/loogle/deploy/live";
      ExecStart = "/home/loogle/deploy/live/server.py";
      NoNewPrivileges = true;
      ProtectSystem = "strict";
      ProtectHome = "read-only";
    };
    unitConfig = {
      ConditionPathExists = "/home/loogle/deploy/live";
    };
  };

  # inspired by https://superuser.com/a/1276457
  systemd.services.loogle-watcher = {
    description = "Loogle file watcher";
    serviceConfig = {
      Type = "oneshot";
      ExecStart="systemctl restart loogle.service";
    };
  };
  systemd.paths.loogle-watcher = {
    wantedBy = [ "multi-user.target" ];
    pathConfig = {
      PathChanged = [
        "/home/loogle/deploy"
      ];
    };
  };

  systemd.services.loogle-updater = {
    wants = ["network-online.target"];
    after = ["network-online.target"];

    serviceConfig = {
      User = "loogle";
      WorkingDirectory = "~";
      ExecStart = "${self.packages.${pkgs.system}.loogle-updater}/bin/loogle-updater /home/loogle";
#      Restart = "on-failure";
      NoNewPrivileges = true;
      ProtectSystem = "strict";
      PrivateTmp = true;
    };
    unitConfig = {
      StartLimitIntervalSec = "10";
      StartLimitBurst = "3";
    };
  };
  systemd.timers.loogle-updater = {
    wantedBy = [ "timers.target" ];
    timerConfig.OnCalendar = "00/6:00"; #  repeat every 6 hours
    timerConfig.Persistent = true;
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
