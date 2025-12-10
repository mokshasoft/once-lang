{
  description = "Once - Write once, compile anywhere";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        haskellPackages = pkgs.haskellPackages;

        # Build without running tests (tests need the built executable in PATH)
        once = pkgs.haskell.lib.dontCheck (haskellPackages.callCabal2nix "once" ./compiler { });
      in
      {
        packages = {
          default = once;
          once = once;
        };

        apps.default = {
          type = "app";
          program = "${once}/bin/once";
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            # Haskell toolchain
            haskellPackages.ghc
            haskellPackages.cabal-install
            pkgs.stack
            haskellPackages.haskell-language-server

            # Formatting
            haskellPackages.fourmolu

            # Build tools
            pkgs.gcc

            # Agda for formal verification
            pkgs.agda
            pkgs.agdaPackages.standard-library

            # Development utilities
            pkgs.git
          ];

          # Set up Agda library path
          AGDA_DIR = "${pkgs.agdaPackages.standard-library}/share/agda";

          shellHook = ''
            echo "Once development environment"
            echo "  ghc:    $(ghc --version)"
            echo "  stack:  $(stack --version | head -1)"
            echo "  gcc:    $(gcc --version | head -1)"
            echo "  agda:   $(agda --version)"
            echo ""
            echo "Commands:"
            echo "  stack build    - Build the compiler"
            echo "  stack test     - Run tests"
            echo "  nix build      - Build with Nix"
            echo "  agda formal/Once/Category/Laws.agda - Type check Agda proofs"
          '';
        };
      }
    );
}
