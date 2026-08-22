------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — THE ⌜Hom⌝/⌜Nat⌝ BRIDGE, ORDER REFLEXIVITY, `m ≤ suc m`.
--
-- ★ WHY THIS MODULE EXISTS.  Seven `Lib*` modules build on `⊢le-refl` /
--   `reflTm` / `natAsEl` / `El-homNat`, so a LIBRARY was importing an
--   EXAMPLE.  These are the primitives; `…ExamplesStrong` keeps the
--   strong-induction ASSEMBLY, which is the actual demonstration.
--
-- ⚠ FUTURE.md's split table was WRONG about one row.  It listed "the
--   `⊢le-refl-z/s` demos" as staying behind.  They are not demos —
--   `⊢le-refl` IS `natrec ⊢reflMot ⊢le-refl-z ⊢le-refl-s`, so they are its
--   two branches.  `⊢le-suc` moved for the same reason, one level out:
--   `⊢pred-le` in `…LibMonus` is defined by it.
--   ⇒ classify by what a primitive is DEFINED BY, not by how it reads.
--
-- ⚠ `…ExamplesStrong` re-exports this module `public`, so every existing
--   importer keeps working unchanged; only `Lib*` importers were repointed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibStrong where


open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Π; lam; app; renTy; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; El-⌜Hom⌝; El-⌜Nat⌝; ξ-Homᵀ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; ⊢unit; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢absurd; ⊢ordtr; ⊢⌜Hom⌝; ⊢⌜Nat⌝
        ; ⊢lam; ⊢app; there; nrs; single
        ; _⊢ty_; ty-El; ty-Nat; ty-U; ty-Π; ty-Hom; wk-single )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
------------------------------------------------------------------------
-- 0. The one conversion everything below is built from: the ⌜Hom⌝ CODE
--    at ⌜Nat⌝ decodes to the computing order.  Two steps — decode the
--    hom, then decode the ambient.
------------------------------------------------------------------------

El-homNat : {Γ : Cx} (a b : RTm Γ) → El (⌜Hom⌝ ⌜Nat⌝ a b) ⟶ᵀ* Hom Nat a b
El-homNat a b = stepᵀ (El-⌜Hom⌝ ⌜Nat⌝ a b) (stepᵀ (ξ-Homᵀ El-⌜Nat⌝) doneᵀ)

-- a `Nat` variable, seen as a member of the DECODED code — the one
-- coercion `⊢⌜Hom⌝` needs, since it takes its endpoints at `El c`.
natAsEl : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
natAsEl d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

-- ★ …and the other direction, which gap A's equation 4 needs.  `⊢congAt`'s
--   family is typed in `Γ ▹ El ⌜Nat⌝`, so the `natrec` scrutinee arrives at
--   `El ⌜Nat⌝` and has to be read back as a `Nat`.
elAsNat : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
elAsNat d = ⊢conv d (credᵀ El-⌜Nat⌝)

------------------------------------------------------------------------
-- ★★★ 1. `m ≤ m` AT AN OPEN NATURAL.
--
--   The motive is the CODE `⌜Hom⌝ ⌜Nat⌝ m m`, which is why this is
--   expressible at all: stage C made the order type SMALL, so it can be
--   a `natrec` motive.
--
--   ★ THE POINT: the successor branch is `⊢var here` — THE IH, UNCHANGED.
--     No lemma, no congruence, no rewriting.  `Hom Nat (suc m) (suc m)`
--     REDUCES to `Hom Nat m m` (`Hom-Nat-ss`), so the IH already has the
--     goal's type.  Anywhere else this is `cong suc` on a ≤-derivation.
------------------------------------------------------------------------

reflMot : {Γ : Cx} → RTy (Γ ∙)
reflMot = El (⌜Hom⌝ ⌜Nat⌝ (var vz) (var vz))

reflTm : {Γ : Cx} → RTm Γ → RTm Γ
reflTm m = natrec unit (var vz) m

⊢reflMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty reflMot
⊢reflMot = ty-El (⊢⌜Hom⌝ ⊢⌜Nat⌝ (natAsEl (⊢var here)) (natAsEl (⊢var here)))

-- the code at the ZERO instance collapses all the way to `Unit`.
⊢le-refl-z : {Γ : Ctx} → Γ ⊢ unit ∷ El (⌜Hom⌝ ⌜Nat⌝ nzero nzero)
⊢le-refl-z =
  ⊢conv ⊢unit
    (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans (El-homNat nzero nzero)
                              (stepᵀ (Hom-Nat-z nzero) doneᵀ))))

-- ★ the successor branch: the IH's type and the goal BOTH reduce to
--   `Hom Nat n n`, so the branch is the variable itself.
⊢le-refl-s : {Γ : Ctx} →
             ((Γ ▹ Nat) ▹ reflMot) ⊢ var vz
               ∷ El (⌜Hom⌝ ⌜Nat⌝ (nsuc (var (vs vz))) (nsuc (var (vs vz))))
⊢le-refl-s =
  ⊢conv (⊢var here)
        (ctrnᵀ (red→≅ᵀ (El-homNat (var (vs vz)) (var (vs vz))))
               (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
                 (El-homNat (nsuc (var (vs vz))) (nsuc (var (vs vz))))
                 (stepᵀ (Hom-Nat-ss (var (vs vz)) (var (vs vz))) doneᵀ)))))

-- ★★ REFLEXIVITY OF THE ORDER, at an arbitrary open natural.
⊢le-refl : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} →
           Γ ⊢ m ∷ Nat → Γ ⊢ reflTm m ∷ Hom Nat m m
⊢le-refl {m = m} dm =
  ⊢conv (⊢natrec ⊢reflMot ⊢le-refl-z ⊢le-refl-s dm)
        (red→≅ᵀ (El-homNat m m))

------------------------------------------------------------------------
-- ★★ 2. `m ≤ suc m`, the other everyday ≤-lemma, same shape.
--     The zero case is `Hom Nat 0 1 ⟶ᵀ Unit`; the successor case is
--     again the bare IH.
------------------------------------------------------------------------

sucMot : {Γ : Cx} → RTy (Γ ∙)
sucMot = El (⌜Hom⌝ ⌜Nat⌝ (var vz) (nsuc (var vz)))

⊢sucMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty sucMot
⊢sucMot =
  ty-El (⊢⌜Hom⌝ ⊢⌜Nat⌝ (natAsEl (⊢var here)) (natAsEl (⊢nsuc (⊢var here))))

⊢le-suc : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} →
          Γ ⊢ m ∷ Nat → Γ ⊢ natrec unit (var vz) m ∷ Hom Nat m (nsuc m)
⊢le-suc {m = m} dm =
  ⊢conv (⊢natrec ⊢sucMot zBranch sBranch dm)
        (red→≅ᵀ (El-homNat m (nsuc m)))
  where
    zBranch : {Γ : Ctx} → Γ ⊢ unit ∷ El (⌜Hom⌝ ⌜Nat⌝ nzero (nsuc nzero))
    zBranch =
      ⊢conv ⊢unit
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans (El-homNat nzero (nsuc nzero))
                                  (stepᵀ (Hom-Nat-z (nsuc nzero)) doneᵀ))))

    sBranch : {Γ : Ctx} →
              ((Γ ▹ Nat) ▹ sucMot) ⊢ var vz
                ∷ El (⌜Hom⌝ ⌜Nat⌝ (nsuc (var (vs vz)))
                                  (nsuc (nsuc (var (vs vz)))))
    sBranch =
      ⊢conv (⊢var here)
            (ctrnᵀ (red→≅ᵀ (El-homNat (var (vs vz)) (nsuc (var (vs vz)))))
                   (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
                     (El-homNat (nsuc (var (vs vz)))
                                (nsuc (nsuc (var (vs vz)))))
                     (stepᵀ (Hom-Nat-ss (var (vs vz)) (nsuc (var (vs vz))))
                            doneᵀ)))))
