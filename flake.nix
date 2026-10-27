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
        # The source is compiler/ plus the root LICENSE: compiler/LICENSE is a
        # symlink to ../LICENSE, which dangles in a source of compiler/ alone.
        onceSrc = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [ ./compiler ./LICENSE ];
        };
        onceUnwrapped = pkgs.haskell.lib.compose.overrideCabal (_: {
          src = onceSrc;
          postUnpack = "sourceRoot=$sourceRoot/compiler";
        }) (pkgs.haskell.lib.dontCheck (haskellPackages.callCabal2nix "once" ./compiler { }));

        # Plan 0.125: the shape of the nixpkgs package. Strata is installed to
        # share/once/Strata (the compiler's installed fallback); binutils is
        # appended to PATH so a user's own as/ld (or AS/LD) still win.
        once = pkgs.haskell.lib.compose.overrideCabal (old: {
          pname = "once-lang";
          buildTools = (old.buildTools or [ ]) ++ [ pkgs.makeWrapper ];
          postInstall = (old.postInstall or "") + ''
            mkdir -p $out/share/once
            cp -r --no-preserve=mode ${./Strata} $out/share/once/Strata
            find $out/share/once/Strata -name '*.o' -delete
            wrapProgram $out/bin/once --suffix PATH : ${pkgs.lib.makeBinPath [ pkgs.binutils ]}
          '';
          mainProgram = "once";
        }) (pkgs.haskell.lib.compose.justStaticExecutables onceUnwrapped);
      in
      {
        packages = {
          default = once;
          once = once;
          once-lang = once;
        };

        apps.default = {
          type = "app";
          program = "${once}/bin/once";
        };

        devShells = {
          # Default: full development environment
          default = self.devShells.${system}.full;

          # Compiler-only: minimal shell for Haskell compiler development
          compiler = pkgs.mkShell {
            buildInputs = [
              haskellPackages.ghc
              haskellPackages.cabal-install
              pkgs.stack
              haskellPackages.haskell-language-server
              haskellPackages.fourmolu
              pkgs.gcc
              pkgs.git
            ];

            shellHook = ''
              if [ -t 0 ] && [ -z "$ONCE_QUIET" ]; then
                echo "Once compiler development (minimal)"
                echo "  ghc:   $(ghc --version)"
                echo "  cabal: $(cabal --version | head -1)"
                echo "  gcc:   $(gcc --version | head -1)"
                echo ""
                echo "For full environment: nix develop .#full"
              fi
            '';
          };

          # x86-64: native compilation (same as default but explicit)
          x86-64 = pkgs.mkShell {
            buildInputs = [
              haskellPackages.ghc
              haskellPackages.cabal-install
              pkgs.stack
              pkgs.gcc
              pkgs.qemu
              pkgs.git
            ];

            shellHook = ''
              if [ -t 0 ] && [ -z "$ONCE_QUIET" ]; then
                echo "Once x86-64 development"
                echo "  gcc:  $(gcc --version | head -1)"
                echo "  qemu: $(qemu-system-x86_64 --version | head -1)"
              fi
            '';
          };

          # ARM64: cross-compilation for AArch64
          arm64 = pkgs.mkShell {
            buildInputs = [
              haskellPackages.ghc
              haskellPackages.cabal-install
              pkgs.stack
              pkgs.pkgsCross.aarch64-multiplatform.buildPackages.gcc
              pkgs.qemu
              pkgs.git
            ];

            shellHook = ''
              if [ -t 0 ] && [ -z "$ONCE_QUIET" ]; then
                echo "Once ARM64 cross-compilation"
                echo "  gcc:  $(aarch64-unknown-linux-gnu-gcc --version | head -1)"
                echo "  qemu: $(qemu-system-aarch64 --version | head -1)"
              fi
            '';
          };

          # RISC-V 64: cross-compilation for RISC-V
          riscv64 = pkgs.mkShell {
            buildInputs = [
              haskellPackages.ghc
              haskellPackages.cabal-install
              pkgs.stack
              pkgs.pkgsCross.riscv64.buildPackages.gcc
              pkgs.qemu
              pkgs.git
            ];

            shellHook = ''
              if [ -t 0 ] && [ -z "$ONCE_QUIET" ]; then
                echo "Once RISC-V 64 cross-compilation"
                echo "  gcc:  $(riscv64-unknown-linux-gnu-gcc --version | head -1)"
                echo "  qemu: $(qemu-system-riscv64 --version | head -1)"
              fi
            '';
          };

          # Agda: formal verification only
          agda = pkgs.mkShell {
            buildInputs = [
              pkgs.agda
              pkgs.agdaPackages.standard-library
              pkgs.git
            ];

            AGDA_DIR = "${pkgs.agdaPackages.standard-library}/share/agda";

            shellHook = ''
              if [ -t 0 ] && [ -z "$ONCE_QUIET" ]; then
                echo "Once formal verification"
                echo "  agda: $(agda --version)"
                echo ""
                echo "Run: cd formal && make"
              fi
            '';
          };

          # Full: everything (original behavior)
          full = pkgs.mkShell {
            buildInputs = [
              haskellPackages.ghc
              haskellPackages.cabal-install
              pkgs.stack
              haskellPackages.haskell-language-server
              haskellPackages.fourmolu
              pkgs.gcc
              pkgs.pkgsCross.aarch64-multiplatform.buildPackages.gcc
              pkgs.pkgsCross.riscv64.buildPackages.gcc
              pkgs.qemu
              pkgs.agda
              pkgs.agdaPackages.standard-library
              pkgs.git
            ];

            AGDA_DIR = "${pkgs.agdaPackages.standard-library}/share/agda";

            shellHook = ''
              if [ -t 0 ] && [ -z "$ONCE_QUIET" ]; then
                echo "Once full development environment"
                echo "  ghc:   $(ghc --version)"
                echo "  cabal: $(cabal --version | head -1)"
                echo "  gcc:   $(gcc --version | head -1)"
                echo "  agda:  $(agda --version)"
                echo ""
                echo "Cross-compilers: aarch64-unknown-linux-gnu-gcc, riscv64-unknown-linux-gnu-gcc"
                echo "QEMU: qemu-system-{x86_64,aarch64,riscv64}"
              fi
            '';
          };
        };
      }
    );
}
