{
  description = "seL4 + Once Language Echo Server Example";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";

    # Once compiler from parent flake
    once-lang.url = "path:../..";

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

  outputs = { self, nixpkgs, flake-utils, once-lang
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

        # Once compiler from parent flake
        onceCompiler = once-lang.packages.${system}.once;

        # Strata directory with seL4 interpretations
        strataDir = ../../Strata;

        # Once source files
        onceRootserver = ../../examples/seL4/Rootserver/Rootserver-simple.once;
        onceEchoClient = ../../examples/seL4/EchoServer/echo-client-simple.once;
        onceEchoServer = ../../examples/seL4/EchoServer/EchoServer.once;

        # Compile Once files to C
        onceCompiledC = pkgs.runCommand "once-compiled-c" {
          nativeBuildInputs = [ onceCompiler ];
        } ''
          mkdir -p $out

          # Compile echo client (only uses IPC)
          once build --strata ${strataDir} \
            -I:C I.SeL4.IPC \
            ${onceEchoClient} -o $out/echo_client.c 2>&1 || true

          # Check if generated files exist
          if [ -f "$out/echo_client.c.c" ]; then
            mv $out/echo_client.c.c $out/echo_client.c
          fi

          # List what was generated
          ls -la $out/
        '';

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

        # seL4 source tree with Once Echo server
        seL4-once-src = pkgs.runCommand "seL4-once-src" {} ''
          mkdir -p $out/{kernel,tools/seL4,projects}

          # Core seL4 kernel
          cp -r ${seL4-kernel}/* $out/kernel/

          # seL4 tools
          cp -r ${seL4-tools}/* $out/tools/seL4/

          # Runtime
          mkdir -p $out/projects/sel4runtime
          cp -r ${sel4runtime}/* $out/projects/sel4runtime/

          # Libraries
          mkdir -p $out/projects/seL4_libs
          cp -r ${seL4-libs}/* $out/projects/seL4_libs/

          mkdir -p $out/projects/util_libs
          cp -r ${util_libs}/* $out/projects/util_libs/

          mkdir -p $out/projects/sel4_projects_libs
          cp -r ${sel4_projects_libs}/* $out/projects/sel4_projects_libs/

          # C library
          mkdir -p $out/projects/musllibc
          cp -r ${musllibc}/* $out/projects/musllibc/

          # Once Echo server project
          mkdir -p $out/projects/once-echo/apps/once-echo
          cp -r ${./once-echo}/src $out/projects/once-echo/apps/once-echo/
          cp -r ${./once-echo}/include $out/projects/once-echo/apps/once-echo/ 2>/dev/null || mkdir -p $out/projects/once-echo/apps/once-echo/include

          # Create settings.cmake (just sets up module paths)
          cat > $out/projects/once-echo/settings.cmake << 'SETTINGS_EOF'
#
# Once Echo Server settings for seL4 - Module path setup
#

cmake_minimum_required(VERSION 3.16.0)

set(project_dir "''${CMAKE_CURRENT_LIST_DIR}/../..")
file(GLOB project_modules ''${project_dir}/projects/*)
list(
    APPEND
        CMAKE_MODULE_PATH
        ''${project_dir}/kernel
        ''${project_dir}/tools/seL4/cmake-tool/helpers/
        ''${project_dir}/tools/seL4/elfloader-tool/
        ''${project_modules}
)

set(SEL4_CONFIG_DEFAULT_ADVANCED ON)
SETTINGS_EOF

          # Create top-level CMakeLists.txt (modeled after sel4test)
          cat > $out/projects/once-echo/CMakeLists.txt << 'CMAKE_EOF'
#
# Once Echo Server for seL4
#

cmake_minimum_required(VERSION 3.16.0)

include(settings.cmake)

project(once-echo C ASM)

# Build settings (match sel4test defaults)
set(RELEASE OFF CACHE BOOL "Performance optimized build")
set(VERIFICATION OFF CACHE BOOL "Only verification friendly kernel features")

# Now include application_settings after project() when PLATFORM is available
include(application_settings)

correct_platform_strings()

find_package(seL4 REQUIRED)
sel4_configure_platform_settings()

set(valid_platforms ''${KernelPlatform_all_strings} ''${correct_platform_strings_platform_aliases})
set_property(CACHE PLATFORM PROPERTY STRINGS ''${valid_platforms})
if(NOT "''${PLATFORM}" IN_LIST valid_platforms)
    message(FATAL_ERROR "Invalid PLATFORM selected: \"''${PLATFORM}\"
Valid platforms are: \"''${valid_platforms}\"")
endif()

if(SIMULATION)
    ApplyCommonSimulationSettings(''${KernelSel4Arch})
endif()

# Apply release/verification settings (this enables debug output)
ApplyCommonReleaseVerificationSettings(''${RELEASE} ''${VERIFICATION})

find_package(elfloader-tool REQUIRED)

# Root CNode size
set(KernelRootCNodeSizeBits 13 CACHE INTERNAL "")

sel4_import_kernel()
elfloader_import_project()

add_subdirectory(apps/once-echo)

if(SIMULATION)
    include(simulation)
    if(KernelSel4ArchX86_64)
        SetSimulationScriptProperty(MEM_SIZE "3G")
    endif()
    GenerateSimulateScript()
endif()
CMAKE_EOF

          # Create app CMakeLists.txt
          cat > $out/projects/once-echo/apps/once-echo/CMakeLists.txt << 'APP_EOF'
#
# Once Echo Server Application
#

cmake_minimum_required(VERSION 3.16.0)

project(once-echo C)

find_package(musllibc REQUIRED)
find_package(util_libs REQUIRED)
find_package(seL4_libs REQUIRED)

# Setup build environment with musl libc and sel4runtime
musllibc_setup_build_environment_with_sel4runtime()
sel4_import_libsel4()
util_libs_import_libraries()
sel4_libs_import_libraries()

# Source files
file(GLOB sources src/*.c)

# Create executable
add_executable(once-echo EXCLUDE_FROM_ALL ''${sources})

target_include_directories(once-echo PRIVATE "include" "src")

target_link_libraries(
    once-echo
    PUBLIC
        sel4_autoconf
        muslc
        sel4
        sel4runtime
        sel4allocman
        sel4vka
        sel4utils
        sel4platsupport
        sel4muslcsys
)

target_compile_options(once-echo PRIVATE -Werror -g)

# Declare as rootserver
include(rootserver)
DeclareRootserver(once-echo)
APP_EOF
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
              -C ../projects/sel4test/settings.cmake \
              -DPLATFORM=x86_64 \
              -DSIMULATION=TRUE \
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
  -m size=3G \\
  -kernel $out/images/kernel-x86_64-pc99 \\
  -initrd $out/images/sel4test-driver-image-x86_64-pc99
EOF
            chmod +x $out/bin/simulate
          '';
        };

        # seL4 with Once Echo server
        seL4-once-echo = pkgs.stdenv.mkDerivation {
          pname = "seL4-once-echo";
          version = "0.1.0";

          src = seL4-once-src;

          nativeBuildInputs = with pkgs; [
            cmake
            ninja
            pythonEnv
            dtc
            libxml2
            libxml2.bin
            cpio
            ubootTools
            protobuf
            which
            bash
          ];

          postPatch = ''
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
              -C ../projects/once-echo/settings.cmake \
              -DPLATFORM=x86_64 \
              -DSIMULATION=TRUE \
              ../projects/once-echo

            cd ..
          '';

          buildPhase = ''
            ninja -C build
          '';

          installPhase = ''
            mkdir -p $out/{bin,images}
            cp -r build/images/* $out/images/ || true

            # Create simulate script
            cat > $out/bin/simulate << EOF
#!/bin/sh
exec qemu-system-x86_64 \\
  -cpu Nehalem,-vme,+pdpe1gb,-xsave,-xsaveopt,-xsavec,-fsgsbase,-invpcid,enforce \\
  -nographic -serial mon:stdio \\
  -m size=3G \\
  -kernel $out/images/kernel-x86_64-pc99 \\
  -initrd $out/images/once-echo-image-x86_64-pc99
EOF
            chmod +x $out/bin/simulate
          '';
        };

        # seL4 source tree with Once-language project
        # NOTE: Currently uses handwritten C; Once compilation pending tuple fix
        seL4-once-lang-src = pkgs.runCommand "seL4-once-lang-src" {} ''
          mkdir -p $out/{kernel,tools/seL4,projects}

          # Core seL4 kernel
          cp -r ${seL4-kernel}/* $out/kernel/

          # seL4 tools
          cp -r ${seL4-tools}/* $out/tools/seL4/

          # Runtime
          mkdir -p $out/projects/sel4runtime
          cp -r ${sel4runtime}/* $out/projects/sel4runtime/

          # Libraries
          mkdir -p $out/projects/seL4_libs
          cp -r ${seL4-libs}/* $out/projects/seL4_libs/

          mkdir -p $out/projects/util_libs
          cp -r ${util_libs}/* $out/projects/util_libs/

          mkdir -p $out/projects/sel4_projects_libs
          cp -r ${sel4_projects_libs}/* $out/projects/sel4_projects_libs/

          # C library
          mkdir -p $out/projects/musllibc
          cp -r ${musllibc}/* $out/projects/musllibc/

          # Once Echo server project - compile Once to C
          mkdir -p $out/projects/once-echo/apps/once-echo/src
          mkdir -p $out/projects/once-echo/apps/once-echo/include

          # NOTE: The Once compiler's C backend currently has a bug with tuple destructuring
          # that generates invalid C code (accessing .fst.fst on void* without casts).
          # For now, we use the handwritten C implementations.
          # TODO: Fix Once compiler tuple destructuring and enable Once compilation.

          # Copy all handwritten C implementations
          cp ${./once-echo}/src/main.c $out/projects/once-echo/apps/once-echo/src/
          cp ${./once-echo}/src/echo_server.c $out/projects/once-echo/apps/once-echo/src/
          cp ${./once-echo}/src/echo_server.h $out/projects/once-echo/apps/once-echo/src/
          cp ${./once-echo}/src/echo_client.c $out/projects/once-echo/apps/once-echo/src/

          # Create settings.cmake
          cat > $out/projects/once-echo/settings.cmake << 'SETTINGS_EOF'
#
# Once Echo Server settings for seL4 - Module path setup
#

cmake_minimum_required(VERSION 3.16.0)

set(project_dir "''${CMAKE_CURRENT_LIST_DIR}/../..")
file(GLOB project_modules ''${project_dir}/projects/*)
list(
    APPEND
        CMAKE_MODULE_PATH
        ''${project_dir}/kernel
        ''${project_dir}/tools/seL4/cmake-tool/helpers/
        ''${project_dir}/tools/seL4/elfloader-tool/
        ''${project_modules}
)

set(SEL4_CONFIG_DEFAULT_ADVANCED ON)
SETTINGS_EOF

          # Create top-level CMakeLists.txt
          cat > $out/projects/once-echo/CMakeLists.txt << 'CMAKE_EOF'
#
# Once Echo Server for seL4 (Once Language Edition)
#

cmake_minimum_required(VERSION 3.16.0)

include(settings.cmake)

project(once-echo C ASM)

set(RELEASE OFF CACHE BOOL "Performance optimized build")
set(VERIFICATION OFF CACHE BOOL "Only verification friendly kernel features")

include(application_settings)

correct_platform_strings()

find_package(seL4 REQUIRED)
sel4_configure_platform_settings()

set(valid_platforms ''${KernelPlatform_all_strings} ''${correct_platform_strings_platform_aliases})
set_property(CACHE PLATFORM PROPERTY STRINGS ''${valid_platforms})
if(NOT "''${PLATFORM}" IN_LIST valid_platforms)
    message(FATAL_ERROR "Invalid PLATFORM selected: \"''${PLATFORM}\"
Valid platforms are: \"''${valid_platforms}\"")
endif()

if(SIMULATION)
    ApplyCommonSimulationSettings(''${KernelSel4Arch})
endif()

ApplyCommonReleaseVerificationSettings(''${RELEASE} ''${VERIFICATION})

find_package(elfloader-tool REQUIRED)

set(KernelRootCNodeSizeBits 13 CACHE INTERNAL "")

sel4_import_kernel()
elfloader_import_project()

add_subdirectory(apps/once-echo)

if(SIMULATION)
    include(simulation)
    if(KernelSel4ArchX86_64)
        SetSimulationScriptProperty(MEM_SIZE "3G")
    endif()
    GenerateSimulateScript()
endif()
CMAKE_EOF

          # Create app CMakeLists.txt
          cat > $out/projects/once-echo/apps/once-echo/CMakeLists.txt << 'APP_EOF'
#
# Once Echo Server Application (Once Language Edition)
#

cmake_minimum_required(VERSION 3.16.0)

project(once-echo C)

find_package(musllibc REQUIRED)
find_package(util_libs REQUIRED)
find_package(seL4_libs REQUIRED)

musllibc_setup_build_environment_with_sel4runtime()
sel4_import_libsel4()
util_libs_import_libraries()
sel4_libs_import_libraries()

# Source files - includes Once-compiled C
file(GLOB sources src/*.c)

add_executable(once-echo EXCLUDE_FROM_ALL ''${sources})

target_include_directories(once-echo PRIVATE "include" "src")

target_link_libraries(
    once-echo
    PUBLIC
        sel4_autoconf
        muslc
        sel4
        sel4runtime
        sel4allocman
        sel4vka
        sel4utils
        sel4platsupport
        sel4muslcsys
)

target_compile_options(once-echo PRIVATE -Werror -g)

include(rootserver)
DeclareRootserver(once-echo)
APP_EOF

          echo "Once-language seL4 source tree created."
          ls -la $out/projects/once-echo/apps/once-echo/src/
        '';

        # seL4 with Once-language compiled echo
        seL4-once-lang = pkgs.stdenv.mkDerivation {
          pname = "seL4-once-lang";
          version = "0.1.0";

          src = seL4-once-lang-src;

          nativeBuildInputs = with pkgs; [
            cmake
            ninja
            pythonEnv
            dtc
            libxml2
            libxml2.bin
            cpio
            ubootTools
            protobuf
            which
            bash
          ];

          postPatch = ''
            patchShebangs kernel/tools/
            patchShebangs tools/
          '';

          configurePhase = ''
            cp -r $src/* .
            chmod -R u+w .

            patchShebangs kernel/tools/
            patchShebangs tools/

            mkdir -p build
            cd build
            cmake -G Ninja \
              -DCMAKE_TOOLCHAIN_FILE=../kernel/gcc.cmake \
              -C ../projects/once-echo/settings.cmake \
              -DPLATFORM=x86_64 \
              -DSIMULATION=TRUE \
              ../projects/once-echo

            cd ..
          '';

          buildPhase = ''
            ninja -C build
          '';

          installPhase = ''
            mkdir -p $out/{bin,images}
            cp -r build/images/* $out/images/ || true

            cat > $out/bin/simulate << EOF
#!/bin/sh
exec qemu-system-x86_64 \\
  -cpu Nehalem,-vme,+pdpe1gb,-xsave,-xsaveopt,-xsavec,-fsgsbase,-invpcid,enforce \\
  -nographic -serial mon:stdio \\
  -m size=3G \\
  -kernel $out/images/kernel-x86_64-pc99 \\
  -initrd $out/images/once-echo-image-x86_64-pc99
EOF
            chmod +x $out/bin/simulate
          '';
        };

      in {
        # Packages
        packages = {
          seL4-src = seL4-src;
          seL4-once-src = seL4-once-src;
          seL4-once-lang-src = seL4-once-lang-src;
          seL4-x86_64 = seL4-x86_64;
          seL4-once-echo = seL4-once-echo;
          seL4-once-lang = seL4-once-lang;
          once-compiled-c = onceCompiledC;
          default = seL4-once-echo;
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
