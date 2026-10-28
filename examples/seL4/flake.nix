{
  description = "seL4 + Once: an echo server and client, Once programs on seL4 x86_64 (plan 0.127)";

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
  };

  outputs = { self, nixpkgs, flake-utils, once-lang, seL4-kernel }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; };

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
        ]);

        # The seL4 kernel alone (x86_64, pc99, debug, printing, and
        # seL4_tools' ApplyCommonSimulationSettings: QEMU's TCG has no PCID);
        # the root task is a Once image, given to QEMU as the multiboot module.
        # `kernel32.elf` is the kernel as an elf32 image, the form QEMU's
        # multiboot loader takes. `gen_headers/` keeps the generated syscall
        # and invocation numbers the Host and impl files must agree with.
        seL4-kernel-x86_64 = pkgs.stdenv.mkDerivation {
          pname = "seL4-kernel-x86_64-pc99";
          version = "78c3b11a";
          src = seL4-kernel;
          nativeBuildInputs = with pkgs; [ cmake ninja pythonEnv libxml2 dtc ];
          hardeningDisable = [ "all" ];
          postPatch = "patchShebangs tools/";
          configurePhase = ''
            mkdir build && cd build
            cmake -G Ninja \
              -DCMAKE_TOOLCHAIN_FILE=../gcc.cmake \
              -DKernelPlatform=pc99 \
              -DKernelSel4Arch=x86_64 \
              -DKernelVerificationBuild=OFF \
              -DKernelDebugBuild=ON \
              -DKernelPrinting=ON \
              -DKernelSupportPCID=OFF \
              -DKernelFSGSBase=msr \
              -DKernelIOMMU=OFF \
              -DKernelFPU=FXSAVE \
              ..
          '';
          buildPhase = "ninja kernel.elf";
          installPhase = ''
            mkdir -p $out
            cp kernel.elf $out/
            objcopy -O elf32-i386 kernel.elf $out/kernel32.elf
            cp -r gen_headers $out/
            cp gen_config/kernel/gen_config.h $out/
          '';
        };

        onceCompiler = once-lang.packages.${system}.once;
        strata = "${once-lang}/Strata";

        # The echo image: the root task (Root.once) with the server
        # (program 1) and the client (program 2) linked beside it
        echo-image = pkgs.runCommand "seL4-once-echo-image" {
          nativeBuildInputs = [ onceCompiler pkgs.binutils pkgs.bash ];
        } ''
          mkdir -p $out
          bash ${./link-image.sh} once ${strata} $out/echo-image \
            ${./Echo/Root.once} ${./Echo/Server.once} ${./Echo/Client.once}
        '';

        qemuFlags = "-cpu Nehalem,-vme,+pdpe1gb,-xsave,-xsaveopt,-xsavec,-fsgsbase,-invpcid,enforce"
          + " -display none -monitor none -m size=512M";

        # Boot the image under QEMU; the console is the serial port
        simulate = pkgs.writeShellScriptBin "simulate" ''
          exec ${pkgs.qemu}/bin/qemu-system-x86_64 ${qemuFlags} -serial mon:stdio \
            -kernel ${seL4-kernel-x86_64}/kernel32.elf \
            -initrd ${echo-image}/echo-image
        '';

        # The test: boot, wait for the client's line, check what the Once
        # programs printed (the root task's steps all succeed: seven '0's;
        # the client's line is what the server echoed: A to Z)
        echo-test = pkgs.runCommand "seL4-once-echo-test" {
          nativeBuildInputs = [ pkgs.qemu pkgs.gnugrep pkgs.coreutils ];
        } ''
          serial=$PWD/serial.txt
          timeout 60 qemu-system-x86_64 ${qemuFlags} -serial file:$serial \
            -kernel ${seL4-kernel-x86_64}/kernel32.elf \
            -initrd ${echo-image}/echo-image &
          qemu=$!
          for _ in $(seq 120); do
            grep -q 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' $serial 2>/dev/null && break
            sleep 0.5
          done
          sleep 1
          kill $qemu 2>/dev/null || true
          tr -d '\r' < $serial > console.txt
          cat console.txt
          grep -qx '0000000' console.txt
          grep -qx 'ABCDEFGHIJKLMNOPQRSTUVWXYZ' console.txt
          mkdir -p $out
          cp console.txt $out/
        '';

      in {
        packages = {
          inherit seL4-kernel-x86_64 echo-image echo-test simulate;
          default = echo-test;
        };

        checks.echo = echo-test;

        apps.simulate = {
          type = "app";
          program = "${simulate}/bin/simulate";
        };

        devShells.default = pkgs.mkShell {
          name = "seL4-once-dev";
          buildInputs = [ pkgs.qemu pkgs.binutils onceCompiler ];
        };
      }
    );
}
