{
  description = "seL4 + Once: an echo server and client, Once programs on seL4 (plan 0.127)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";

    # The Once compiler and Strata of this repository (the working tree)
    once-lang.url = "path:../..";

    # The seL4 kernel, pinned (a sel4test-manifest commit)
    seL4-kernel = {
      url = "github:seL4/seL4/78c3b11a02368dadd314e34a61d53853d6a4b2d7";
      flake = false;
    };

    # seL4's loader for riscv64 and the CPIO library it needs
    seL4-tools = {
      url = "github:seL4/seL4_tools/6493e0c6fab360eb81a8115a49c9ca7bc280c48a";
      flake = false;
    };
    util-libs = {
      url = "github:seL4/util_libs/ef49a397b7044fc38b609a99a8c6265a97913b8e";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, once-lang, seL4-kernel, seL4-tools, util-libs }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;

        # Python environment for the seL4 kernel build
        pythonEnv = pkgs.python3.withPackages (ps: with ps; [
          jinja2
          ply
          future
          six
          jsonschema
          pyyaml
          setuptools
          lxml
          # The elfloader's layout tool (shoehorn.py, riscv64)
          libarchive-c
          pyelftools
          sortedcontainers
          # The device-tree parser seL4's hardware_gen.py needs (riscv64)
          (buildPythonPackage rec {
            pname = "pyfdt";
            version = "0.3";
            format = "setuptools";
            src = pkgs.fetchurl {
              url = "https://files.pythonhosted.org/packages/source/p/pyfdt/pyfdt-${version}.tar.gz";
              sha256 = "1w7lp421pssfgv901103521qigwb12i6sk68lqjllfgz0lh1qq31";
            };
            doCheck = false;
          })
        ]);

        commonKernelFlags = [
          "-DKernelVerificationBuild=OFF"
          "-DKernelDebugBuild=ON"
          "-DKernelPrinting=ON"
        ];
        buildTools = with pkgs; [ cmake ninja pythonEnv libxml2 dtc ];

        # One seL4 kernel alone (debug, printing). `gen_headers/` keeps the
        # generated syscall and invocation numbers the Host and impl files
        # must agree with.
        mkKernel = { arch, stdenv, flags, installExtra ? "", tools ? [ ] }: stdenv.mkDerivation {
          pname = "seL4-kernel-${arch}";
          version = "78c3b11a";
          src = seL4-kernel;
          nativeBuildInputs = buildTools ++ tools;
          hardeningDisable = [ "all" ];
          postPatch = "patchShebangs tools/";
          dontStrip = true;
          dontFixup = true;
          configurePhase = ''
            mkdir build && cd build
            cmake -G Ninja \
              -DCMAKE_TOOLCHAIN_FILE=../gcc.cmake \
              ${lib.concatStringsSep " " (commonKernelFlags ++ flags)} \
              ..
          '';
          buildPhase = "ninja kernel.elf";
          installPhase = ''
            mkdir -p $out
            cp kernel.elf $out/
            ${installExtra}
            cp -r gen_headers $out/
            cp gen_config/kernel/gen_config.h $out/
            cp -r autoconf gen_config generated $out/
            find . -name 'shared_types_gen.h' > $out/shared_types_gen.txt
          '';
        };

        # pc99 under QEMU, seL4_tools' ApplyCommonSimulationSettings: TCG has
        # no PCID
        x86Flags = [
          "-DKernelPlatform=pc99"
          "-DKernelSupportPCID=OFF"
          "-DKernelIOMMU=OFF"
          "-DKernelFPU=FXSAVE"
        ];

        # `kernel32.elf` is the kernel as an elf32 image, the form QEMU's
        # multiboot loader takes
        seL4-kernel-x86_64 = mkKernel {
          arch = "x86_64";
          stdenv = pkgs.stdenv;
          flags = x86Flags ++ [ "-DKernelSel4Arch=x86_64" "-DKernelFSGSBase=msr" ];
          installExtra = "objcopy -O elf32-i386 kernel.elf $out/kernel32.elf";
        };

        # ia32 is built by the 32-bit toolchain; its kernel.elf already is elf32
        seL4-kernel-x86_32 = mkKernel {
          arch = "x86_32";
          stdenv = pkgs.pkgsi686Linux.stdenv;
          flags = x86Flags ++ [ "-DKernelSel4Arch=ia32" ];
          installExtra = "cp kernel.elf $out/kernel32.elf";
        };

        # riscv64 (QEMU's virt machine) is cross-built; the kernel's build
        # asks QEMU for the machine's device tree
        riscv64Prefix = "riscv64-unknown-linux-gnu-";
        riscv64Flags = [
          "-DKernelPlatform=qemu-riscv-virt"
          "-DKernelSel4Arch=riscv64"
          "-DCROSS_COMPILER_PREFIX=${riscv64Prefix}"
        ];
        riscv64Binutils = pkgs.pkgsCross.riscv64.buildPackages.binutils-unwrapped;
        seL4-kernel-riscv64 = mkKernel {
          arch = "riscv64";
          stdenv = pkgs.pkgsCross.riscv64.stdenv;
          flags = riscv64Flags;
          tools = [ pkgs.qemu ];
        };

        # On riscv64 a kernel and a root task boot together: seL4's elfloader
        # holds both, and QEMU's OpenSBI starts it (riscv64-boot/CMakeLists.txt)
        mkRiscv64Loader = image: pkgs.pkgsCross.riscv64.stdenv.mkDerivation {
          name = "seL4-once-riscv64-loader";
          dontUnpack = true;
          dontStrip = true;
          dontFixup = true;
          hardeningDisable = [ "all" ];
          nativeBuildInputs = buildTools ++ [ pkgs.qemu pkgs.cpio ];
          configurePhase = ''
            cp -r ${seL4-kernel} kernel
            cp -r ${seL4-tools} tools
            cp -r ${util-libs} util_libs
            chmod -R u+w kernel tools util_libs
            patchShebangs kernel/tools tools
            mkdir build && cd build
            cmake -G Ninja \
              -DCMAKE_TOOLCHAIN_FILE=$PWD/../kernel/gcc.cmake \
              ${lib.concatStringsSep " " (commonKernelFlags ++ riscv64Flags)} \
              -DSEL4_KERNEL=$PWD/../kernel \
              -DSEL4_TOOLS=$PWD/../tools \
              -DUTIL_LIBS=$PWD/../util_libs \
              -DONCE_IMAGE=${image}/image \
              ${./riscv64-boot}
          '';
          buildPhase = "ninja elfloader/elfloader";
          installPhase = ''
            mkdir -p $out
            cp elfloader/elfloader $out/
          '';
        };

        onceCompiler = once-lang.packages.${system}.once;
        strata = "${once-lang}/Strata";

        x86QemuFlags = "-cpu Nehalem,-vme,+pdpe1gb,-xsave,-xsaveopt,-xsavec,-fsgsbase,-invpcid,enforce"
          + " -display none -monitor none -m size=512M";
        x86Boot = kernel: image:
          "qemu-system-x86_64 ${x86QemuFlags} -kernel ${kernel}/kernel32.elf -initrd ${image}/image";

        # One row per architecture: its kernel, the tools that link for it,
        # how QEMU boots an image, the C compiler the number check uses
        arches = {
          x86_64 = {
            kernel = seL4-kernel-x86_64;
            toolEnv = "";
            boot = x86Boot seL4-kernel-x86_64;
            runCC = pkgs.runCommandCC;
          };
          x86_32 = {
            kernel = seL4-kernel-x86_32;
            toolEnv = "";
            boot = x86Boot seL4-kernel-x86_32;
            runCC = pkgs.pkgsi686Linux.runCommandCC;
          };
          riscv64 = {
            kernel = seL4-kernel-riscv64;
            toolEnv = let b = "${riscv64Binutils}/bin/${riscv64Prefix}"; in
              "export AS=${b}as LD=${b}ld OBJCOPY=${b}objcopy";
            boot = image: "qemu-system-riscv64 -machine virt -cpu rv64 -m 3072M"
              + " -display none -monitor none -bios default"
              + " -kernel ${mkRiscv64Loader image}/elfloader";
            runCC = pkgs.runCommandCC;
          };
        };

        # An image: the root task with further programs linked beside it
        mkImage = arch: name: programs: pkgs.runCommand "seL4-once-${name}-image-${arch}" {
          nativeBuildInputs = [ onceCompiler pkgs.binutils pkgs.bash ];
        } ''
          ${arches.${arch}.toolEnv}
          mkdir -p $out
          bash ${./link-image.sh} once ${strata} ${arch} $out/image \
            ${lib.concatMapStringsSep " " (program: "${program}") programs}
        '';

        # The examples: boot, wait for `until` on the console, then `verify`
        # the file console.txt. Each program line is what the Once programs
        # printed; `Once: returned` is the Host's `leave`.
        examples = {
          # The root task's seven steps all succeed (seven '0's); the client's
          # line is what the server echoed
          echo = {
            programs = [ ./Echo/Root.once ./Echo/Server.once ./Echo/Client.once ];
            until = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
            verify = ''
              grep -qx '0000000' console.txt
              grep -qx 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' console.txt
            '';
          };

          # A root task that allocates without bound faults, not a corrupted
          # stack (plan 0.123 A.5): it has no fault endpoint, so the kernel
          # reports the fault and stops it
          exhausted = {
            programs = [ ./Exhausted/Hungry.once ];
            until = "unknown syscall";
            verify = "grep -q 'unknown syscall' console.txt";
          };

          # The same program under a monitor: the kernel sends its fault to
          # the fault endpoint the root task waits on. Four steps succeed,
          # then the fault's label, 2 (seL4_Fault_UnknownSyscall)
          monitored = {
            programs = [ ./Exhausted/Monitor.once ./Exhausted/Hungry.once ];
            until = "Once: returned";
            verify = "grep -qx '00002' console.txt";
          };

          # Message words 2 and 3 of seL4_Call, with the kernel as the other
          # end (on x86_32 they go through the root task's IPC buffer). The
          # last digit reads the third register of a new thread: flags on x86
          words = {
            programs = [ ./Words/Root.once ];
            until = "Once: returned";
            verify = ''
              case $arch in riscv64) want=0001100 ;; *) want=0001101 ;; esac
              grep -qx "$want" console.txt
            '';
          };

          # A root task runs every CNode and Notification operation and prints
          # one digit per step (plan 0.127 D.1). Two steps fail on purpose, and
          # the debug kernel reports each failure in the middle of the
          # program's line (a whole `<<seL4(CPU 0) ...>>` message, colours and
          # newline included): the check removes those and reads the line back
          caps = {
            programs = [ ./Caps/Root.once ];
            until = "Once: returned";
            verify = ''
              sed -E -z 's/\x1b\[[0-9;]*m//g; s/<<seL4[^\n]*>>\n//g' console.txt > program.txt
              grep -qx '00500580060' program.txt
              grep -qx 'Once: returned' program.txt
            '';
          };
        };

        mkTest = arch: name: example:
          let boot = arches.${arch}.boot (mkImage arch name example.programs); in
          pkgs.runCommand "seL4-once-${name}-test-${arch}" {
            nativeBuildInputs = [ pkgs.qemu pkgs.gnugrep pkgs.gnused pkgs.coreutils ];
          } ''
            arch=${arch}
            serial=$PWD/serial.txt
            timeout 120 ${boot} -serial file:$serial &
            qemu=$!
            for _ in $(seq 240); do
              grep -q '${example.until}' $serial 2>/dev/null && break
              sleep 0.5
            done
            sleep 1
            kill $qemu 2>/dev/null || true
            tr -d '\r' < $serial > console.txt
            cat console.txt
            ${example.verify}
            mkdir -p $out
            cp console.txt $out/
          '';

        # Every seL4 number in the seL4 Host and Interpretations (each file's
        # `seL4 numbers` block) against the pinned kernel's headers: every
        # file for this architecture must have the block, and every .once
        # file with one
        mkNumbersCheck = arch: arches.${arch}.runCC "seL4-once-numbers-check-${arch}" {
          nativeBuildInputs = [ pkgs.gawk pkgs.gnugrep ];
        } ''
          cd ${once-lang}
          bash ${./check-numbers.sh} ${seL4-kernel} ${arches.${arch}.kernel} ${arch} \
            Strata/Hosts/SeL4/Host.${arch} Strata/Interpretations/SeL4/*.${arch} \
            $(grep -l '^-- seL4 numbers$' Strata/Interpretations/SeL4/*.once) | tee $out
        '';

        mkSimulate = arch:
          let boot = arches.${arch}.boot (mkImage arch "echo" examples.echo.programs); in
          pkgs.writeShellScriptBin "simulate-${arch}" ''
            export PATH=${pkgs.qemu}/bin:$PATH
            exec ${boot} -serial mon:stdio
          '';

        archNames = builtins.attrNames arches;

        tests = lib.listToAttrs (lib.concatMap (arch:
          lib.mapAttrsToList (name: example:
            lib.nameValuePair "${name}-test-${arch}" (mkTest arch name example)) examples) archNames);

        numbersChecks = lib.listToAttrs (map (arch:
          lib.nameValuePair "numbers-check-${arch}" (mkNumbersCheck arch)) archNames);

        simulators = lib.listToAttrs (map (arch:
          lib.nameValuePair "simulate-${arch}" (mkSimulate arch)) archNames);

        checks = tests // numbersChecks;

      in {
        packages = checks // simulators // {
          inherit seL4-kernel-x86_64 seL4-kernel-x86_32 seL4-kernel-riscv64;
          all = pkgs.linkFarmFromDrvs "seL4-once-all" (builtins.attrValues checks);
          default = tests.echo-test-x86_64;
        };

        inherit checks;

        apps = lib.mapAttrs (name: drv: {
          type = "app";
          program = "${drv}/bin/${name}";
        }) simulators;

        devShells.default = pkgs.mkShell {
          name = "seL4-once-dev";
          buildInputs = [ pkgs.qemu pkgs.binutils onceCompiler ];
        };
      }
    );
}
