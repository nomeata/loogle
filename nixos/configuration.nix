{ config, pkgs, modulesPath, lib, environment, loogle_server, ... }:
{
  imports = [
    (modulesPath + "/virtualisation/digital-ocean-config.nix")
    ./ship.nix
  ];

  nix.settings.substituters = [
    "https://cache.garnix.io"
  ];
  nix.settings.trusted-public-keys = [
    "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g="
  ];

  security.acme.defaults.email = "mail@joachim-breitner.de";
  security.acme.acceptTerms = true;

  services.nginx = {
    enable = true;
    enableReload = true;
    recommendedProxySettings = true;
    recommendedGzipSettings = true;
    recommendedOptimisation = true;
    recommendedTlsSettings = true;
  };

  services.nginx.virtualHosts = {
    "loogle.nomeata.de" = {
      serverAliases = [ ];
      enableACME = true;
      forceSSL = true;
      locations = {
        "/" = {
          proxyPass = "http://localhost:8080";
          extraConfig =
            # required when the target is also TLS server with multiple hosts
            "proxy_ssl_server_name on;" +
            # required when the server wants to use HTTP Authentication
            "proxy_pass_header Authorization;";
        };
      };
    };
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
      User = "ship";
      Restart = "always";
      ExecStart = "${loogle_server}/bin/loogle_server";
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
