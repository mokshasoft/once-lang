{
  description = "seL4 + Once Language Echo Server Example";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # seL4 repositories (pinned to stable versions)
    seL4 = {
      url = "github:seL4/seL4/13.0.0";
      flake = false;
    };
    seL4_tools = {
      url = "github:seL4/seL4_tools/13.0.0";
      flake = false;
    };
    seL4_libs = {
      url = "github:seL4/seL4_libs/13.0.0";
      flake = false;
    };
    util_libs = {
      url = "github:seL4/util_libs/13.0.0";
      flake = false;
    };
    musllibc = {
      url = "github:seL4/musllibc/sel4";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, seL4, seL4_tools, seL4_libs, util_libs, musllibc }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-linux" ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          # Enable cross-compilation
          crossOverlays = [];
        };

        # Cross-compilation toolchains
        crossPkgs = {
          aarch64 = import nixpkgs {
            inherit system;
            crossSystem = {
              config = "aarch64-none-elf";
              libc = "newlib";
            };
          };
          riscv64 = import nixpkgs {
            inherit system;
            crossSystem = {
              config = "riscv64-none-elf";
              libc = "newlib";
            };
          };
          x86_64 = pkgs;  # Native for x86_64
        };

        # Python with seL4 build dependencies
        pythonEnv = pkgs.python3.withPackages (ps: with ps; [
          jinja2
          ply
          pyfdt
          future
          six
          jsonschema
          pyyaml
          ordered-set
        ]);

        # CMake toolchain files for seL4
        toolchainFile = arch: pkgs.writeText "toolchain-${arch}.cmake" ''
          set(CMAKE_SYSTEM_NAME Generic)
          set(CMAKE_SYSTEM_PROCESSOR ${arch})
          ${if arch == "aarch64" then ''
            set(CMAKE_C_COMPILER aarch64-none-elf-gcc)
            set(CMAKE_ASM_COMPILER aarch64-none-elf-gcc)
            set(CROSS_COMPILER_PREFIX aarch64-none-elf-)
          '' else if arch == "riscv64" then ''
            set(CMAKE_C_COMPILER riscv64-none-elf-gcc)
            set(CMAKE_ASM_COMPILER riscv64-none-elf-gcc)
            set(CROSS_COMPILER_PREFIX riscv64-none-elf-)
          '' else ''
            set(CMAKE_C_COMPILER gcc)
            set(CMAKE_ASM_COMPILER gcc)
          ''}
          set(CMAKE_C_FLAGS "-nostdlib -ffreestanding")
          set(CMAKE_EXE_LINKER_FLAGS "-nostdlib")
        '';

        # seL4 source directory setup
        seL4Sources = pkgs.runCommand "seL4-sources" {} ''
          mkdir -p $out/kernel
          mkdir -p $out/tools/seL4
          mkdir -p $out/libs/seL4_libs
          mkdir -p $out/libs/util_libs
          mkdir -p $out/libs/musllibc

          cp -r ${seL4}/* $out/kernel/
          cp -r ${seL4_tools}/* $out/tools/seL4/
          cp -r ${seL4_libs}/* $out/libs/seL4_libs/
          cp -r ${util_libs}/* $out/libs/util_libs/
          cp -r ${musllibc}/* $out/libs/musllibc/
        '';

        # Once compiler (from parent flake)
        onceCompiler = pkgs.haskellPackages.callCabal2nix "once" ../../compiler {};

        # Build seL4 kernel for a specific platform
        buildSeL4Kernel = { platform, arch }: pkgs.stdenv.mkDerivation {
          name = "seL4-kernel-${platform}";
          src = seL4Sources;

          nativeBuildInputs = with pkgs; [
            cmake
            ninja
            pythonEnv
            dtc
            libxml2
          ] ++ (if arch == "aarch64" then [
            pkgsCross.aarch64-embedded.buildPackages.gcc
          ] else if arch == "riscv64" then [
            pkgsCross.riscv64-embedded.buildPackages.gcc
          ] else [
            gcc
          ]);

          configurePhase = ''
            mkdir -p build
            cd build
            cmake -G Ninja \
              -DCMAKE_TOOLCHAIN_FILE=${toolchainFile arch} \
              -DPLATFORM=${platform} \
              -DKernelVerificationBuild=OFF \
              -DKernelDebugBuild=ON \
              ../kernel
          '';

          buildPhase = ''
            ninja
          '';

          installPhase = ''
            mkdir -p $out
            cp kernel.elf $out/
            cp kernel.dtb $out/ 2>/dev/null || true
          '';
        };

        # Build Once program for seL4
        buildOnceSeL4 = { name, src, arch }: pkgs.stdenv.mkDerivation {
          inherit name src;

          nativeBuildInputs = with pkgs; [
            onceCompiler
          ] ++ (if arch == "aarch64" then [
            pkgsCross.aarch64-embedded.buildPackages.gcc
          ] else if arch == "riscv64" then [
            pkgsCross.riscv64-embedded.buildPackages.gcc
          ] else [
            gcc
          ]);

          buildPhase = ''
            once build --exe --interp ../../Strata/Interpretations/seL4 ${src} -o $name
            ${if arch == "aarch64" then "aarch64-none-elf-gcc"
              else if arch == "riscv64" then "riscv64-none-elf-gcc"
              else "gcc"} \
              -nostdlib -ffreestanding -o $name.elf $name.c
          '';

          installPhase = ''
            mkdir -p $out/bin
            cp $name.elf $out/bin/
          '';
        };

        # QEMU simulation scripts
        simulateArm = pkgs.writeShellScriptBin "simulate-arm" ''
          ${pkgs.qemu}/bin/qemu-system-aarch64 \
            -machine virt \
            -cpu cortex-a53 \
            -m 512 \
            -nographic \
            -kernel "$1"
        '';

        simulateX86 = pkgs.writeShellScriptBin "simulate-x86" ''
          ${pkgs.qemu}/bin/qemu-system-x86_64 \
            -machine q35 \
            -m 512 \
            -nographic \
            -kernel "$1"
        '';

        simulateRiscv = pkgs.writeShellScriptBin "simulate-riscv" ''
          ${pkgs.qemu}/bin/qemu-system-riscv64 \
            -machine virt \
            -m 512 \
            -nographic \
            -kernel "$1"
        '';

      in {
        # Development shell with all tools
        devShells.default = pkgs.mkShell {
          name = "seL4-once-dev";

          buildInputs = with pkgs; [
            # Build tools
            cmake
            ninja
            gnumake

            # Python for seL4 build
            pythonEnv

            # Cross-compilers
            pkgsCross.aarch64-embedded.buildPackages.gcc
            pkgsCross.riscv64-embedded.buildPackages.gcc

            # Utilities
            dtc
            libxml2

            # QEMU for simulation
            qemu

            # Once compiler
            onceCompiler
          ];

          shellHook = ''
            export SEL4_KERNEL=${seL4}
            export SEL4_TOOLS=${seL4_tools}
            export SEL4_LIBS=${seL4_libs}
            export UTIL_LIBS=${util_libs}
            export MUSLLIBC=${musllibc}

            echo "seL4 + Once Development Environment"
            echo ""
            echo "Available commands:"
            echo "  simulate-arm <kernel.elf>    - Run ARM64 in QEMU"
            echo "  simulate-x86 <kernel.elf>    - Run x86_64 in QEMU"
            echo "  simulate-riscv <kernel.elf>  - Run RISC-V64 in QEMU"
            echo ""
            echo "seL4 sources available at:"
            echo "  \$SEL4_KERNEL   - seL4 kernel"
            echo "  \$SEL4_TOOLS    - seL4 build tools"
            echo "  \$SEL4_LIBS     - seL4 libraries"
          '';
        };

        # Packages
        packages = {
          # seL4 kernels for different platforms
          seL4-arm64 = buildSeL4Kernel {
            platform = "qemu-arm-virt";
            arch = "aarch64";
          };

          seL4-riscv64 = buildSeL4Kernel {
            platform = "qemu-riscv-virt";
            arch = "riscv64";
          };

          seL4-x86_64 = buildSeL4Kernel {
            platform = "x86_64";
            arch = "x86_64";
          };

          # QEMU simulation scripts
          inherit simulateArm simulateX86 simulateRiscv;

          # seL4 sources (for reference)
          seL4-sources = seL4Sources;
        };

        # Apps for running simulations
        apps = {
          simulate-arm = {
            type = "app";
            program = "${simulateArm}/bin/simulate-arm";
          };
          simulate-x86 = {
            type = "app";
            program = "${simulateX86}/bin/simulate-x86";
          };
          simulate-riscv = {
            type = "app";
            program = "${simulateRiscv}/bin/simulate-riscv";
          };
        };
      }
    );
}
