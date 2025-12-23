{
  description = "seL4 + Once Language Echo Server Example";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";

    # Use sel4test-manifest for known-working versions
    sel4test-manifest = {
      url = "github:seL4/sel4test-manifest";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, sel4test-manifest }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Python environment for seL4 build
        pythonEnv = pkgs.python3.withPackages (ps: with ps; [
          jinja2
          ply
          future
          six
          jsonschema
          pyyaml
          setuptools
          pexpect
          sortedcontainers
          protobuf
        ]);

        # Repo tool for seL4
        repoTool = pkgs.gitRepo;

      in {
        # Development shell with all tools needed to build seL4
        devShells.default = pkgs.mkShell {
          name = "seL4-once-dev";

          buildInputs = with pkgs; [
            # Build tools
            cmake
            ninja
            gnumake
            ccache

            # Repo tool
            repoTool

            # Python for seL4 build
            pythonEnv

            # Cross-compilers
            pkgsCross.aarch64-embedded.buildPackages.gcc
            pkgsCross.aarch64-embedded.buildPackages.binutils

            # Native compiler for x86_64
            gcc
            binutils

            # Utilities
            dtc
            libxml2
            cpio
            ubootTools  # for mkimage

            # QEMU for simulation
            qemu

            # Haskell for Once compiler
            (haskellPackages.ghcWithPackages (hs: with hs; [
              megaparsec
              mtl
              text
              containers
              optparse-applicative
            ]))
            stack
          ];

          shellHook = ''
            echo "=========================================="
            echo "seL4 + Once Development Environment"
            echo "=========================================="
            echo ""
            echo "Quick start for seL4:"
            echo "  1. mkdir sel4test && cd sel4test"
            echo "  2. repo init -u https://github.com/seL4/sel4test-manifest.git"
            echo "  3. repo sync"
            echo "  4. mkdir build && cd build"
            echo "  5. ../init-build.sh -DPLATFORM=x86_64 -DSIMULATION=TRUE"
            echo "  6. ninja"
            echo "  7. ./simulate"
            echo ""
            echo "For Once compiler:"
            echo "  cd ../../compiler && stack build"
            echo ""
          '';
        };

        # Simplified shell just for QEMU testing
        devShells.qemu = pkgs.mkShell {
          name = "seL4-qemu";
          buildInputs = [ pkgs.qemu ];
        };
      }
    );
}
