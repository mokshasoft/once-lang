# The nixpkgs package for Once (plan 0.125 §3, D341). It goes to
# pkgs/by-name/on/once-lang/package.nix; test it from a nixpkgs checkout with
# `nix-build -A once-lang`, or here with packaging/nixpkgs/test.nix.
# The Haskell part is `cabal2nix ./compiler`, inlined; regenerate it when the
# cabal file's dependencies change.
{
  lib,
  haskell,
  haskellPackages,
  fetchFromGitHub,
  makeWrapper,
  binutils,
}:

let
  version = "0.1.0.0";

  src = fetchFromGitHub {
    owner = "mokshasoft";
    repo = "once-lang";
    # At the release: tag = "v${version}";
    rev = "aef06161cf5b9216a86414080a9bebfbc2e9c74f";
    hash = "sha256-RlBQ/NdC3j7Jxv0qzKGCUhNol4AN7oW3jgEl5Mqg8jA=";
  };

  once = haskellPackages.callPackage (
    {
      mkDerivation,
      base,
      bytestring,
      containers,
      directory,
      filepath,
      process,
      tasty,
      tasty-hunit,
      tasty-quickcheck,
      temporary,
      text,
    }:
    mkDerivation {
      pname = "once-lang";
      inherit version src;
      # compiler/LICENSE is a symlink to ../LICENSE, so unpack the whole
      # repository and build in compiler/.
      postUnpack = "sourceRoot=$sourceRoot/compiler";
      isLibrary = true;
      isExecutable = true;
      libraryHaskellDepends = [
        base
        containers
        directory
        filepath
        process
        text
      ];
      executableHaskellDepends = [
        base
        text
      ];
      testHaskellDepends = [
        base
        bytestring
        containers
        directory
        filepath
        process
        tasty
        tasty-hunit
        tasty-quickcheck
        temporary
        text
      ];
      # The suite runs the built `once` from PATH and the riscv64 cases need a
      # cross binutils and qemu-riscv64; it is run in the repository's CI.
      doCheck = false;
      homepage = "https://github.com/mokshasoft/once-lang";
      description = "Compiler for Once, a verified pure functional language of categorical morphisms";
      license = lib.licenses.agpl3Plus;
      mainProgram = "once";
    }
  ) { };
in
haskell.lib.compose.overrideCabal (old: {
  buildTools = (old.buildTools or [ ]) ++ [ makeWrapper ];
  # The interpretations are read from <bindir>/../share/once/Strata (D341);
  # binutils comes last on PATH, so a user's own as/ld (or AS/LD) win.
  postInstall = (old.postInstall or "") + ''
    mkdir -p $out/share/once
    cp -r --no-preserve=mode ${src}/Strata $out/share/once/Strata
    wrapProgram $out/bin/once --suffix PATH : ${lib.makeBinPath [ binutils ]}
  '';
  maintainers = [ ];
  platforms = lib.platforms.linux;
}) (haskell.lib.compose.justStaticExecutables once)
