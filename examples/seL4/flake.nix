{
  description = "seL4 + Once Language Echo Server Example";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";

    # seL4 repositories - pinned to sel4test-manifest commits
    seL4-kernel = {
      url = "github:seL4/seL4/78c3b11a02368dadd314e34a61d53853d6a4b2d7";
      flake = false;
    };
    seL4-tools = {
      url = "github:seL4/seL4_tools/fbfc6397803b54a809f1995e844c04877fdde006";
      flake = false;
    };
    seL4-libs = {
      url = "github:seL4/seL4_libs/2580739bde15ec0dac1bef43a4e313e3752b7692";
      flake = false;
    };
    sel4test = {
      url = "github:seL4/sel4test/0bbb0c6be4e98df98a04b045f98c5a9d272295b2";
      flake = false;
    };
    sel4runtime = {
      url = "github:seL4/sel4runtime/86489cf6efab9f314964e79468c036e9035394c7";
      flake = false;
    };
    musllibc = {
      url = "github:seL4/musllibc/b0005f86fecbd6d0257b15363a5b013446914265";
      flake = false;
    };
    util_libs = {
      url = "github:seL4/util_libs/07a7e15b845b08edf91e6d65919aaeef1ae4d5eb";
      flake = false;
    };
    sel4_projects_libs = {
      url = "github:seL4/sel4_projects_libs/0e06bebf4a3f0c21317c6877e0079f637e021562";
      flake = false;
    };
    nanopb = {
      url = "github:nanopb/nanopb/1466e6f953835b191a7f5acf0c06c941d4cd33d9";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils
            , seL4-kernel, seL4-tools, seL4-libs, sel4test, sel4runtime
            , musllibc, util_libs, sel4_projects_libs, nanopb }:
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
          lxml
        ]);

        # Combined seL4 source tree (mimics repo manifest structure)
        seL4-src = pkgs.runCommand "seL4-src" {} ''
          mkdir -p $out/{kernel,tools/seL4,projects}

          # Core seL4 kernel
          cp -r ${seL4-kernel}/* $out/kernel/

          # seL4 tools (must be under tools/seL4/ per settings.cmake)
          cp -r ${seL4-tools}/* $out/tools/seL4/

          # Runtime (in projects/)
          mkdir -p $out/projects/sel4runtime
          cp -r ${sel4runtime}/* $out/projects/sel4runtime/

          # Libraries (all in projects/)
          mkdir -p $out/projects/seL4_libs
          cp -r ${seL4-libs}/* $out/projects/seL4_libs/

          mkdir -p $out/projects/util_libs
          cp -r ${util_libs}/* $out/projects/util_libs/

          mkdir -p $out/projects/sel4_projects_libs
          cp -r ${sel4_projects_libs}/* $out/projects/sel4_projects_libs/

          # Test framework
          mkdir -p $out/projects/sel4test
          cp -r ${sel4test}/* $out/projects/sel4test/

          # C library (in projects/)
          mkdir -p $out/projects/musllibc
          cp -r ${musllibc}/* $out/projects/musllibc/

          # nanopb for protobuf support
          mkdir -p $out/tools/nanopb
          cp -r ${nanopb}/* $out/tools/nanopb/
        '';

        # seL4 build for x86_64 simulation
        seL4-x86_64 = pkgs.stdenv.mkDerivation {
          pname = "seL4-test-x86_64";
          version = "master";

          src = seL4-src;

          nativeBuildInputs = with pkgs; [
            cmake
            ninja
            pythonEnv
            dtc
            libxml2
            libxml2.bin  # for xmllint
            cpio
            ubootTools
            protobuf
            which
            bash
          ];

          postPatch = ''
            # Fix shebangs in kernel tools
            patchShebangs kernel/tools/
            patchShebangs tools/
          '';

          configurePhase = ''
            # seL4 build expects writable source tree
            cp -r $src/* .
            chmod -R u+w .

            # Fix shebangs after copy
            patchShebangs kernel/tools/
            patchShebangs tools/

            mkdir -p build
            cd build
            cmake -G Ninja \
              -DCMAKE_TOOLCHAIN_FILE=../kernel/gcc.cmake \
              -DPLATFORM=x86_64 \
              -DSIMULATION=TRUE \
              -DLibSel4FunctionAttributes=public \
              ../projects/sel4test

            # Stay in build dir for next phases
            cd ..
          '';

          buildPhase = ''
            ninja -C build
          '';

          installPhase = ''
            mkdir -p $out/{bin,images}
            cp -r build/images/* $out/images/ || true

            # Create simulate script (multiboot for ELF image)
            cat > $out/bin/simulate << EOF
#!/bin/sh
exec qemu-system-x86_64 \\
  -cpu Nehalem,-vme,+pdpe1gb,-xsave,-xsaveopt,-xsavec,-fsgsbase,-invpcid,enforce \\
  -nographic -serial mon:stdio \\
  -m size=512M \\
  -kernel $out/images/kernel-x86_64-pc99 \\
  -initrd $out/images/sel4test-driver-image-x86_64-pc99
EOF
            chmod +x $out/bin/simulate
          '';
        };

      in {
        # Packages
        packages = {
          seL4-src = seL4-src;
          seL4-x86_64 = seL4-x86_64;
          default = seL4-x86_64;
        };

        # Development shell with all tools
        devShells.default = pkgs.mkShell {
          name = "seL4-once-dev";

          buildInputs = with pkgs; [
            # Build tools
            cmake
            ninja
            gnumake
            ccache
            which

            # Python for seL4 build
            pythonEnv

            # Cross-compilers (for ARM builds)
            pkgsCross.aarch64-embedded.buildPackages.gcc
            pkgsCross.aarch64-embedded.buildPackages.binutils

            # Native compiler for x86_64
            gcc
            binutils

            # Utilities
            dtc
            libxml2
            cpio
            ubootTools
            protobuf

            # QEMU for simulation
            qemu

            # Haskell for Once compiler
            stack
          ];

          shellHook = ''
            echo "=========================================="
            echo "seL4 + Once Development Environment"
            echo "=========================================="
            echo ""
            echo "seL4 sources: ${seL4-src}"
            echo ""
            echo "Build seL4 directly:"
            echo "  nix build .#seL4-x86_64"
            echo "  ./result/bin/simulate"
            echo ""
            echo "Interactive build:"
            echo "  cp -r ${seL4-src} ./seL4-work && chmod -R u+w ./seL4-work"
            echo "  cd seL4-work && mkdir build && cd build"
            echo "  cmake -G Ninja -DPLATFORM=x86_64 -DSIMULATION=TRUE ../projects/sel4test"
            echo "  ninja"
            echo "  ./simulate"
            echo ""
            echo "For Once compiler:"
            echo "  cd ../../compiler && stack build"
            echo ""

            export SEL4_SRC="${seL4-src}"
          '';
        };

        # Shell just for QEMU testing
        devShells.qemu = pkgs.mkShell {
          name = "seL4-qemu";
          buildInputs = [ pkgs.qemu ];
        };
      }
    );
}
