# RELEASE — tagging a version of Once

A release is an annotated tag `v<version>` on a commit of `master`, with the version in the cabal
file and the changelog, and the nixpkgs package pointed at the tag. It gives a fixed point to build,
package and compare against (for example, the baseline of a performance measurement). Releases are
made from `master` only, after the work in them has merged (`MERGE.md`); a release never carries
work of its own.

## 1. The version number

The version follows the Haskell Package Versioning Policy, `A.B.C.D`, as `compiler/once.cabal`
declares (`compiler/CHANGELOG.md` says so too):

- `A.B` (major): bumped when a program that compiled before may no longer compile or may mean
  something else (a change to the language or the Spec's meaning). `A` stays `0` until the language
  is declared stable.
- `C` (minor): bumped when something is added and every earlier program keeps its meaning (new
  language features, new targets, new Interpretations, cheaper code).
- `D` (patch): bumped for fixes and packaging that change no program's meaning.

A version is used once. A pushed tag is never moved or deleted: a mistake in a release is fixed by
the next version.

## 2. Check `master`

```
git checkout master && git pull --ff-only origin master
git status                     # clean
git tag --list 'v*'            # the version is not taken
```

`master` passed `make merge-gate` when its last branch merged. The release re-checks what the
merge gate does not cover, the extracted compiler and the binaries it emits. Run the builds and
tests memory-capped, as for a merge (`MERGE.md` §4); the cabal build uses the same cap as Agda:

```
cd compiler && systemd-run --user --scope --quiet -p MemoryMax=5500M -p MemorySwapMax=2G -- \
  bash -c 'exec cabal build all && cabal test'
cd .. && tests/run-exit-tests.sh && tests/run-exit-tests-x86_32.sh && tests/run-exit-tests-riscv64.sh
```

A failure stops the release: it is fixed on a branch and merged first.

## 3. Measure

Record what the release's emitted code costs, so later work can be compared with it:

```
tests/codegen-measure.sh measure <scratch>/v<version>
```

The totals it prints go into the changelog entry (§4). The full `costs.tsv` is not committed; it
is regenerated from the tag when needed (§7).

## 4. The release commit and the tag

1. `compiler/once.cabal`: `version:` set to the new version.
2. `compiler/CHANGELOG.md`: the `## Unreleased` items move under `## <version> - <YYYY-MM-DD>`,
   with one paragraph saying what the release is (the plans merged since the previous one) and the
   totals of §3. `## Unreleased` stays, empty.
3. `cabal build exe:once` (capped, as in §2): the build reports `once-<version>`.
4. Commit, tag, push:

   ```
   git add compiler/once.cabal compiler/CHANGELOG.md
   git commit -m "Release <version>: <one line on what it is>"
   git tag -a v<version> -m "Once <version>: <the same line>"
   git push origin master && git push origin v<version>
   git ls-remote --tags origin    # the tag is on origin
   ```

## 5. The nixpkgs package

`packaging/nixpkgs/once-lang/package.nix` fetches the release by its tag. A tagged tree cannot
contain the hash of its own source, so the package is updated in the commit after the tag:

```
h=$(nix-prefetch-url --unpack --type sha256 \
      https://github.com/mokshasoft/once-lang/archive/refs/tags/v<version>.tar.gz)
nix hash convert --hash-algo sha256 --to sri "$h"
```

In `package.nix`: `version = "<version>";`, `tag = "v${version}";`, and `hash` set to the SRI hash
printed. Then build the package against the nixpkgs the flake pins, and check its version:

```
nix-build packaging/nixpkgs/test.nix
readlink result                # …-once-lang-<version>
./result/bin/once --help       # the binary runs
```

Commit (`Nix: the once-lang package at <version>, fetched by its tag v<version>`) and push. If the
package also lives in a nixpkgs checkout (`pkgs/by-name/on/once-lang/package.nix`), the same file is
copied there and proposed upstream.

## 6. The GitHub release page (optional)

The tag is the release. A page with notes can be added from the tag, with the changelog entry as
its text: in the web interface, or `gh release create v<version> --notes-file <entry>`.

## 7. Comparing against a release

```
git worktree add ../once-v<version> v<version>
(cd ../once-v<version>/compiler && cabal build exe:once)     # capped, as in §2
tests/codegen-measure.sh measure <scratch>/base "$(cd ../once-v<version>/compiler && cabal list-bin once)"
tests/codegen-measure.sh measure <scratch>/now
tests/codegen-measure.sh compare <scratch>/base/costs.tsv <scratch>/now/costs.tsv
git worktree remove ../once-v<version>
```

The script of the current tree measures both compilers, so the corpus and the columns are the
same on both sides. Its totals for the release match the release's changelog entry; a difference
means the measurement changed, and is said so in the comparison.
