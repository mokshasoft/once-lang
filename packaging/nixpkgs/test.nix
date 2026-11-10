# Builds the nixpkgs package against the nixpkgs this repository's flake pins,
# the way `nix-build -A once-lang` would in a checkout:
#   nix-build packaging/nixpkgs/test.nix
let
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);
  pinned = lock.nodes.nixpkgs.locked;
  nixpkgs = fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${pinned.rev}.tar.gz";
    sha256 = pinned.narHash;
  };
  pkgs = import nixpkgs { };
in
pkgs.callPackage ./once-lang/package.nix { }
