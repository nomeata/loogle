# Shipnix recommended settings
# IMPORTANT: These settings are here for ship-nix to function properly on your server
# Modify with care

{ config, pkgs, modulesPath, lib, ... }:
{
  nix = {
    package = pkgs.nixUnstable;
    extraOptions = ''
      experimental-features = nix-command flakes ca-derivations
    '';
    settings = {
      trusted-users = [ "root" "ship" "nix-ssh" ];
    };
  };

  programs.git.enable = true;
  programs.git.config = {
    advice.detachedHead = false;
  };

  services.openssh = {
    enable = true;
    # ship-nix uses SSH keys to gain access to the server
    # Manage permitted public keys in the `authorized_keys` file
    settings.PasswordAuthentication = false;
    #  permitRootLogin = "no";
  };


  users.users.ship = {
    isNormalUser = true;
    extraGroups = [ "wheel" "nginx" ];
    # If you don't want public keys to live in the repo, you can remove the line below
    # ~/.ssh will be used instead and will not be checked into version control. 
    # Note that this requires you to manage SSH keys manually via SSH,
    # and your will need to manage authorized keys for root and ship user separately
    openssh.authorizedKeys.keyFiles = [ ./authorized_keys ];
    openssh.authorizedKeys.keys = [
      "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABgQCdN5uww1gN8pGFR9/68qZexX+VPYSLmOCiLBd11HrwRm4wowD+01GRRQegTvQqSKfMvVF3SE7bAutZKx3YL9GBoYCCgcHowXqQlpqbFR3bIr8Euh7BechvCXWXiSAkhaUoOW4USW8ZlcQtHyqy4AbKlp2IOCR7M/IncfJM9rxZBPwDLDPzU498n/xlTC2FbHQNwpVP+nSQqJDcc97rwb8HfqhFpaTpvT6l9Bqwh11Y+VgcenEOzvcLQ694+mt+HApkZUBzuukzvu+iyewT5YPA12rEISKT7bhiYiy/vkva/SShXMRPOg6trW1pj4Q18SmtDgI0h16/oZBxUW0kSO6CzVXDR133tU8K+LPziYBm+8fiIySlxbKO70/t0Morujm/1OMgVYiPq1+uOHpT8mPhwm1lIcd95C9FnA+CmzOrKUWxy05iG68pqgMIAVKVczdpsYM3LOGgeasPtdjNgj5jhb4FqWtn2YU3fkBbUp5gHfZVlZ4XTgYmrAEH/6gXZ2s= ship@tite-ship"
      "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIJRd0CZZQXyKTEQSEtrIpcTg15XEoRjuYodwo0nr5hNj jojo@kirk"
    ];
  };

  # Can be removed if you want authorized keys to only live on server, not in repository
  # Se note above for users.users.ship.openssh.authorizedKeys.keyFiles
  users.users.root.openssh.authorizedKeys.keyFiles = [ ./authorized_keys ];
  users.users.root.openssh.authorizedKeys.keys = [
    "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABgQCdN5uww1gN8pGFR9/68qZexX+VPYSLmOCiLBd11HrwRm4wowD+01GRRQegTvQqSKfMvVF3SE7bAutZKx3YL9GBoYCCgcHowXqQlpqbFR3bIr8Euh7BechvCXWXiSAkhaUoOW4USW8ZlcQtHyqy4AbKlp2IOCR7M/IncfJM9rxZBPwDLDPzU498n/xlTC2FbHQNwpVP+nSQqJDcc97rwb8HfqhFpaTpvT6l9Bqwh11Y+VgcenEOzvcLQ694+mt+HApkZUBzuukzvu+iyewT5YPA12rEISKT7bhiYiy/vkva/SShXMRPOg6trW1pj4Q18SmtDgI0h16/oZBxUW0kSO6CzVXDR133tU8K+LPziYBm+8fiIySlxbKO70/t0Morujm/1OMgVYiPq1+uOHpT8mPhwm1lIcd95C9FnA+CmzOrKUWxy05iG68pqgMIAVKVczdpsYM3LOGgeasPtdjNgj5jhb4FqWtn2YU3fkBbUp5gHfZVlZ4XTgYmrAEH/6gXZ2s= ship@tite-ship"
    "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIJRd0CZZQXyKTEQSEtrIpcTg15XEoRjuYodwo0nr5hNj jojo@kirk"
  ];

  security.sudo.extraRules = [
    {
      users = [ "ship" ];
      commands = [
        {
          command = "ALL";
          options = [ "NOPASSWD" "SETENV" ];
        }
      ];
    }
  ];
}
