------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — NATURAL-NUMBER PRIMITIVES.
--
-- ★ WHY THIS MODULE EXISTS.  `plusTm`/`⊢plus` are not examples: four
--   `Lib*` modules build on them, including the arithmetic used by the WF
--   layer.  They lived in `…ExamplesNat` only because that is where they
--   were first written, which made LIBRARIES import EXAMPLES.
--
--   The dependency graph was always acyclic and one-way, so this was a
--   NAMING problem rather than a structural one — but the name was
--   actively misleading about what is load-bearing.
--
-- ⚠ `…ExamplesNat` re-exports this module `public`, so every existing
--   importer keeps working unchanged.  Only `Lib*` importers were
--   repointed, which is the whole point: no library imports an example.
--
-- ★ DESIGN POINT (inherited from `…ExamplesNat`): `natrec` is
--   TYPE-motived — the motive lives in the DERIVATION only — because code
--   motives would need `⌜Nat⌝ ∈ U`, which is stage C.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibNat where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; RTm; var; vz; nsuc; natrec; Nat )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢var; here; ⊢nsuc; ⊢natrec; ty-Nat )

-- Term: `natrec z s n`; `s` has TWO binders (the number, then the IH).
plusTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
plusTm m n = natrec n (nsuc (var vz)) m

-- the CONSTANT-Nat motive makes every obligation definitional
⊢plus : {Γ : Ctx} {m n : RTm ⌊ Γ ⌋} →
        Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ plusTm m n ∷ Nat
⊢plus dm dn = ⊢natrec ty-Nat dn (⊢nsuc (⊢var here)) dm
