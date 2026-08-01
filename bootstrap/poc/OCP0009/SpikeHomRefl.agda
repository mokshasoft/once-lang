------------------------------------------------------------------------
-- OCP-0009 · W2 eliminator step — HOW DOES `refl` COMPUTE?
--
-- The kernel derives directed paths at UNFOLDABLE `Hom` types by computation
-- alone (`⊢hom-id`: the identity map inhabits `Hom U c c`).  At the STUCK
-- heads — `base`, neutral `El`, `Σ'`, higher `Hom` — nothing inhabits `Hom`
-- yet, and the congruence floor demands an identity path at every type.  So
-- `refl` must be a TERM former.  The design question is how it computes,
-- because a `refl` typed at an unfoldable `Hom` (`Hom (Π A B) f f` unfolds
-- to a `Π`!) must itself reduce to a lambda, or canonicity and the LR's
-- `Π`-membership both break — a stuck non-neutral term at a `Π` type is a
-- member of nothing.
--
-- Raw reduction cannot see types.  Two candidate designs:
--
--   (A) `refl : RTy Γ → RTm Γ → RTm Γ` — TYPE-annotated.  Then the
--       annotation must reduce (`refl (El c) t` with `c ⟶ ⌜Π⌝ …` must
--       unfold eventually), so `_⟶_` needs `ξ-refl-ty : A ⟶ᵀ A' → …` —
--       a TYPE-reduction premise inside TERM reduction.  Since `_⟶ᵀ_`
--       already contains `_⟶_` (via `ξ-El`), the two relations become
--       MUTUAL, and with them the whole confluence development: `Conf`'s
--       free-standing term triangle and `Inj`'s type triangle merge into
--       one mutual Takahashi development.  That cost is structural and
--       permanent — it removes the property that term confluence stands
--       alone, which this cascade just verified twice ("Conf untouched").
--
--   (B) ★ `hrefl : RTm Γ → RTm Γ → RTm Γ` — CODE-annotated, TAKEN.  The
--       annotation is a TERM (a code), so all congruences stay inside
--       `_⟶_` and the reduction relations remain STRATIFIED.  The price:
--
--         * a `⌜Hom⌝` CODE must be added so that `refl` at higher paths
--           (`Hom (Hom …) p p`) is expressible — semantically honest:
--           hom-sets of small types are small.  Predicativity is
--           untouched (`⌜Hom⌝` quantifies over codes and terms, never `U`;
--           there is still no code for `U`).
--         * `El (⌜Hom⌝ c t u) ⟶ᵀ Hom (El c) t u` joins the decode rules.
--         * ⚠ the level-0 LR clause for `Hom` RETURNS: with a `⌜Hom⌝`
--           code, small types CAN reduce to `Hom`s, so cascade 3/3's
--           finding 2 ("level 0 needs no Hom clause") is REPEALED by this
--           step, and `homSem₀` (the level-0 mirror of `homSem₁`) is owed.
--           Known shape, bounded cost — priced, not discovered mid-proof.
--
--       Coverage under (B): small types via `hrefl` (including small `Σ'`
--       and higher paths via `⌜Hom⌝`); `base` itself via `hrefl ⌜base⌝`
--       plus one `⊢conv` step (`Hom (El ⌜base⌝) t t ≅ᵀ Hom base t t`);
--       LARGE unfoldable types by computation (the `⊢hom-id` pattern,
--       pointwise down to leaves).  ⚠ The one GAP: `Hom` at a LARGE `Σ'`
--       (one mentioning `U`) is stuck and code-less, so it has no `refl`
--       until `Σ'`'s unfolding lands with transport.  Documented, temporary.
--
-- ★ MEASURED BELOW: (B)'s unfolding function is structurally terminating —
-- no pragma, no measure, no sized types — because the ONLY recursive clause
-- descends into the code `⌜Π⌝`'s codomain, and every stuck clause returns a
-- canonical form.  Same result shape as `SpikeHomTy` item 1.
--
-- `--safe`, zero postulates, zero holes, zero imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeHomRefl where

------------------------------------------------------------------------
-- 1. The miniature calculus: codes (with `⌜Hom⌝`) and the term fragment
--    `hrefl`'s unfolding constructs.  Scoping elided (as in `SpikeHomTy`):
--    binders do not affect the termination measure.
------------------------------------------------------------------------

data Cd : Set
data Tm : Set

data Cd where
  cb    : Cd                  -- ⌜base⌝
  cΠ cΣ : Cd → Cd → Cd        -- ⌜Π⌝ / ⌜Σ⌝
  cH    : Cd → Tm → Tm → Cd   -- ★ ⌜Hom⌝: code + two endpoints
  cne   : Tm → Cd             -- a neutral term in code position

data Tm where
  v0     : Tm
  wk     : Tm → Tm
  lam    : Tm → Tm
  app    : Tm → Tm → Tm
  hrefl  : Cd → Tm → Tm       -- ★ the annotated refl: `hrefl c t : Hom (El c) t t`

------------------------------------------------------------------------
-- 2. ★ THE UNFOLDING, and the termination check.
--
-- `hunfold c t` is the normal form of `hrefl c t` w.r.t. the refl rules
-- alone.  Read against the kernel's `Hom` clauses: `hrefl` unfolds exactly
-- where `Hom` does (minus `U`, where refl needs no primitive at all — the
-- identity lambda is already there) and is a CANONICAL FORM exactly where
-- `Hom` is stuck.
------------------------------------------------------------------------

hunfold : Cd → Tm → Tm

-- ★ the one recursive clause — pointwise refl, descending into the CODE's
-- codomain, a strict subterm.  Kernel rule it stands for:
--   hrefl (⌜Π⌝ c d) f ⟶ lam (hrefl d (app (wk f) v0))
hunfold (cΠ c d) t = lam (hunfold d (app (wk t) v0))

-- stuck — CANONICAL inhabitants of the stuck `Hom`s:
hunfold cb         t = hrefl cb t              -- refl at (El ⌜base⌝ ⟶ᵀ) base
hunfold (cΣ c d)   t = hrefl (cΣ c d) t        -- Hom at Σ' awaits transport
hunfold (cH c a b) t = hrefl (cH c a b) t      -- higher refl: refl at a path type
hunfold (cne n)    t = hrefl (cne n) t         -- neutral code: genuinely stuck

------------------------------------------------------------------------
-- 3. WHAT THIS SETTLES, and what the consolidation still owes.
--
-- ★ SETTLED: design (B).  `hunfold` is accepted with no TERMINATING pragma
-- and no measure; reduction stays stratified (`_⟶_` alone carries every
-- refl rule, including the code congruence `ξ-hreflˡ : c ⟶ c' → …`); and
-- higher refl is expressible through `⌜Hom⌝`.  Design (A) is REJECTED on
-- the recorded cost: it makes `_⟶_`/`_⟶ᵀ_` mutual and merges the two
-- confluence developments — permanent structural damage for no expressive
-- gain over (B) + `⌜Hom⌝`.
--
-- ⚠ NOT SETTLED HERE (the consolidation's bill, priced):
--   1. New TERM formers `⌜Hom⌝`/`hrefl` — the §3.1 flip condition charges
--      for the first time: SN/SNe/SNRed cases, `sn-anti` lines, `Conf`'s
--      term development gains real cases (`hrefl (⌜Π⌝ c d) f` unfold vs
--      congruence — the same one-step-behind pattern as `Hom-Π`).
--   2. `El (⌜Hom⌝ c t u) ⟶ᵀ Hom (El c) t u` — decode rule, `Inj`'s `⁺ᵀ`
--      and triangle gain the matching cases.
--   3. The level-0 `Hom` clause + `homSem₀` (finding 2 of cascade 3/3 is
--      repealed by `⌜Hom⌝` — that finding was ABOUT the code-less kernel).
--   4. Typing: `⊢⌜Hom⌝ : c ∷ U → t ∷ El c → u ∷ El c → ⌜Hom⌝ c t u ∷ U`
--      and `⊢hrefl : c ∷ U → t ∷ El c → hrefl c t ∷ Hom (El c) t t`;
--      `sr` for the unfold rule; `fund` cases via `homSem₀`/`⊩`-membership
--      of canonical `hrefl` at stuck `Hom`s (membership is `SN`, and
--      `hrefl` normal forms are SN — `sn-hrefl` mirrors `sn-cΠ`).
------------------------------------------------------------------------
