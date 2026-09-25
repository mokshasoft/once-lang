------------------------------------------------------------------------
-- PROBE — `Examples/Scoped.agda`'s TWIN, indexed by CONTEXT AND TYPE.
--
--   Scoped (baseline):  Tm n            -- index: a DEPTH (one ℕ)
--   here   (probe):     Tm (Γ , A)      -- index: a CONTEXT and a TYPE
--
-- Same language, same two interesting constructors.  The ONLY
-- difference is the index, which is the whole question:
--
--     lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
--     app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
--
-- ★★★ THE RESULT, measured 2026-09-23 (standalone, warm deps):
--
--     | | lines (lam+app, desc+Wf) | module | time | memory |
--     | `Scoped`   depth-indexed |  22 | 433 | 0.68 s | 171 MB |
--     | `ScopedTy` type-indexed  |  96 | 257 | 0.42 s | 159 MB |
--
--   ⇒ the CONSTRUCTORS cost **4.4×** the lines.  ⇒ there is **NO time
--     or memory blowup at all** — the type-indexed module is FASTER and
--     SMALLER than its depth-indexed baseline.
--
--   ⚠ NOT apples-to-apples on the module totals: `Scoped` carries `var`
--     and the whole forded `Fin` family, which this file omits;
--     this file carries the `Ty` and `Ctx` families, which `Scoped`
--     does not need (a depth is a ℕ, already a kernel type).  The
--     4.4× on lam+app IS apples-to-apples — both have exactly those
--     two constructors.
--
-- ★ THE PREDICTION, from `Scoped`'s own header — *"`iι` targets the
--   AMBIENT index, so a constructor that wants to land at `suc m` must
--   SAY SO with an `Id` field"*:
--
--     `app`  target IS the ambient `(Γ , B)`      ⇒ NO Ford, +1 κ for A
--     `lam`  target is `(Γ , A ⇒ B)` ≠ ambient    ⇒ FORD, +3 κ
--
--   ⇒ the delta is ONE Ford and four κ fields.  Everything else is the
--   two auxiliary datatypes the index is built from.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedTy where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; DescWf; dwf-nil; dwf-cons; DConWf; dwf-ι; dwf-ρ; dwf-κ
        ; ⊢⌜Mu⌝; ⊢⌜Σ⌝; ⊢⌜Id⌝; ⊢conv; ⊢pair; ⊢fst; ⊢snd; ⊢con; ⊢unit
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ ; Θ₀; ρ₀; x₀; _,,_; ICodeWf; icw-clo; icw-ford
        ; IDescWf; idwf-nil; idwf-cons; ty-Σ; ty-El; ty-Mu; ty-Unit
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜Σ⌝; El-⌜Mu⌝ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; Mu; IMu; El; Σ'; U; _∈D_; hereD; thereD
        ; Desc; dnil; _◃_; DCon; dι; dρ; dκ
        ; IDesc; inil; _◂_; ICon; iι; iρ; iκ
        ; con; pair; fst; snd; unit; ⌜Mu⌝; ⌜Σ⌝; ⌜Id⌝ )

------------------------------------------------------------------------
-- 1. THE TWO AUXILIARY DATATYPES the index is built from.
--    ⚠ `Scoped`'s index needed NONE of this — `INat = El ⌜Nat⌝`, one
--      line, because a depth is a ℕ and ℕ is already a kernel type.
------------------------------------------------------------------------

-- Ty ::= base | Ty ⇒ Ty
TyD : Desc
TyD = dι ◃ (dρ (dρ dι) ◃ dnil)

Ty : {Γ : Cx} → RTy Γ
Ty = Mu TyD

⌜Ty⌝ : {Γ : Cx} → RTm Γ
⌜Ty⌝ = ⌜Mu⌝ TyD

base : {Γ : Cx} → RTm Γ
base = con 0 unit

arrow : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
arrow a b = con 1 (pair a (pair b unit))

-- Ctx ::= nil | Ty , Ctx
CtxD : Desc
-- ⚠ the field type must be `El c` for a CLOSED code `c` (`dwf-κ`),
--   which is `Scoped`'s `INat = El ⌜Nat⌝` trick one level down.
CtxD = dι ◃ (dκ (El (⌜Mu⌝ TyD)) (dρ dι) ◃ dnil)

Cxt : {Γ : Cx} → RTy Γ
Cxt = Mu CtxD

⌜Cxt⌝ : {Γ : Cx} → RTm Γ
⌜Cxt⌝ = ⌜Mu⌝ CtxD

nilC : {Γ : Cx} → RTm Γ
nilC = con 0 unit

consC : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
consC a g = con 1 (pair a (pair g unit))

------------------------------------------------------------------------
-- 2. THE INDEX — a PAIR of them.
--    ★ `Scoped` uses `El ⌜Nat⌝` so the index type is the DECODE of a
--      code; mirrored here so `ty-IMu` obligations line up the same way.
------------------------------------------------------------------------

⌜I⌝ : {Γ : Cx} → RTm Γ
⌜I⌝ = ⌜Σ⌝ ⌜Cxt⌝ ⌜Ty⌝

I : RTy ε
I = El ⌜I⌝

ix : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
ix g a = pair g a

------------------------------------------------------------------------
-- 3. THE CONSTRUCTORS — and the whole probe is the difference between
--    these two and `Scoped`'s.
--
--   Scoped (depth):   lamC = iρ (nsuc (var vz)) iι              -- 1 field
--                     appC = iρ (var vz) (iρ (var (vs vz)) iι)  -- 2 fields
------------------------------------------------------------------------

-- app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
-- ★ TARGET IS THE AMBIENT `(Γ , B)`, so NO Ford — exactly as predicted.
--   `A` is a parameter, so it is a κ field; `A ⇒ B` is BUILT from it
--   and the ambient's second component, which is forward.
appC : ICon (ε ∙)
appC =
  iκ ⌜Ty⌝                                              -- A
   (iρ (ix (fst (var (vs vz)))                         -- Γ
           (arrow (var vz) (snd (var (vs vz)))))       -- A ⇒ B
    (iρ (ix (fst (var (vs (vs vz))))                   -- Γ
            (var (vs vz)))                             -- A
     iι))

-- lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
-- ⚠ TARGET IS `(Γ , A ⇒ B)`, NOT the ambient ⇒ it must SAY SO with an
--   `Id` field.  That is the one Ford, and the three κ fields the
--   depth-indexed version does not need.
lamC : ICon (ε ∙)
lamC =
  iκ ⌜Ty⌝                                              -- A
   (iκ ⌜Ty⌝                                            -- B
    (iκ ⌜Cxt⌝                                          -- Γ
     (iρ (ix (consC (var (vs (vs vz))) (var vz))       -- (Γ , A)
             (var (vs vz)))                            -- B
      (iκ (⌜Id⌝ ⌜I⌝ (var (vs (vs (vs (vs vz)))))       -- the FORD
                    (ix (var (vs vz))
                        (arrow (var (vs (vs (vs vz))))
                               (var (vs (vs vz))))))
       iι))))

TmD : IDesc
TmD = appC ◂ (lamC ◂ inil)

Tm : {Γ : Cx} → RTm Γ → RTy Γ
Tm i = IMu TmD I i

------------------------------------------------------------------------
-- 4. WELL-FORMEDNESS.
------------------------------------------------------------------------

TyWf : DescWf TyD
TyWf = dwf-cons dwf-ι (dwf-cons (dwf-ρ (dwf-ρ dwf-ι)) dwf-nil)

CtxWf : DescWf CtxD
CtxWf = dwf-cons dwf-ι
          (dwf-cons (dwf-κ (⌜Mu⌝ TyD) (⊢⌜Mu⌝ TyWf) (dwf-ρ dwf-ι)) dwf-nil)

⊢⌜Ty⌝ : {Γ : Ctx} → Γ ⊢ ⌜Ty⌝ ∷ U
⊢⌜Ty⌝ = ⊢⌜Mu⌝ TyWf

⊢⌜Cxt⌝ : {Γ : Ctx} → Γ ⊢ ⌜Cxt⌝ ∷ U
⊢⌜Cxt⌝ = ⊢⌜Mu⌝ CtxWf

⊢⌜I⌝ : {Γ : Ctx} → Γ ⊢ ⌜I⌝ ∷ U
⊢⌜I⌝ = ⊢⌜Σ⌝ ⊢⌜Cxt⌝ ⊢⌜Ty⌝

------------------------------------------------------------------------
-- 5. THE CONVERSIONS the index costs — one per `⌜Mu⌝`, plus the `Σ`.
--    ⚠ `Scoped` needs exactly ONE of these (`elNat`).  A pair index
--      over two datatypes needs THREE.
------------------------------------------------------------------------

elΣI : {Γ : Cx} → El (⌜I⌝ {Γ}) ≅ᵀ Σ' (El ⌜Cxt⌝) (El ⌜Ty⌝)
elΣI = credᵀ (El-⌜Σ⌝ _ _)

elMuTy : {Γ : Cx} → El (⌜Ty⌝ {Γ}) ≅ᵀ Mu TyD
elMuTy = credᵀ El-⌜Mu⌝

elMuCx : {Γ : Cx} → El (⌜Cxt⌝ {Γ}) ≅ᵀ Mu CtxD
elMuCx = credᵀ El-⌜Mu⌝

------------------------------------------------------------------------
-- 6. BUILDING AND DESTRUCTING AN INDEX.
------------------------------------------------------------------------

⊢ixP : {Γ : Ctx} {g a : RTm ⌊ Γ ⌋} →
       Γ ⊢ g ∷ El ⌜Cxt⌝ → Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ ix g a ∷ El ⌜I⌝
⊢ixP dg da = ⊢conv (⊢pair (ty-El ⊢⌜Ty⌝) dg da) (csymᵀ elΣI)

⊢fstI : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} →
        Γ ⊢ i ∷ El ⌜I⌝ → Γ ⊢ fst i ∷ El ⌜Cxt⌝
⊢fstI di = ⊢fst (⊢conv di elΣI)

⊢sndI : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} →
        Γ ⊢ i ∷ El ⌜I⌝ → Γ ⊢ snd i ∷ El ⌜Ty⌝
⊢sndI di = ⊢snd (⊢conv di elΣI)

------------------------------------------------------------------------
-- 7. THE TWO TYPE CONSTRUCTORS, TYPED.
--    ⚠ `Scoped` needs NONE of this — its index is `nsuc`, a kernel
--      constructor with `⊢nsuc` already proved.
------------------------------------------------------------------------

⊢base : {Γ : Ctx} → Γ ⊢ base ∷ El ⌜Ty⌝
⊢base = ⊢conv (⊢con TyWf hereD ⊢unit) (csymᵀ elMuTy)

⊢arrow : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ b ∷ El ⌜Ty⌝ → Γ ⊢ arrow a b ∷ El ⌜Ty⌝
⊢arrow da db =
  ⊢conv (⊢con TyWf (thereD hereD)
           (⊢pair (ty-Σ (ty-Mu TyWf) ty-Unit) (⊢conv da elMuTy)
             (⊢pair ty-Unit (⊢conv db elMuTy) ⊢unit)))
        (csymᵀ elMuTy)

⊢nilC : {Γ : Ctx} → Γ ⊢ nilC ∷ El ⌜Cxt⌝
⊢nilC = ⊢conv (⊢con CtxWf hereD ⊢unit) (csymᵀ elMuCx)

⊢consC : {Γ : Ctx} {a g : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ g ∷ El ⌜Cxt⌝ → Γ ⊢ consC a g ∷ El ⌜Cxt⌝
⊢consC da dg =
  ⊢conv (⊢con CtxWf (thereD hereD)
           (⊢pair (ty-Σ (ty-Mu CtxWf) ty-Unit) da
             (⊢pair ty-Unit (⊢conv dg elMuCx) ⊢unit)))
        (csymᵀ elMuCx)

------------------------------------------------------------------------
-- 8. ★★★ THE TWO WELL-FORMEDNESS PROOFS — the measurement.
--
--   `Scoped`'s, for comparison:
--       lamWf = iwf-ρ (nsuc (var vz)) (toI (⊢nsuc (fromI (⊢var here)))) iwf-ι
--       appWf = iwf-ρ (var vz) (⊢var here)
--                (iwf-ρ (var (vs vz)) (⊢var (there here)) iwf-ι)
------------------------------------------------------------------------

appWf : IConWf I (Θ₀ I) ρ₀ x₀ appC
appWf =
  iwf-κ ⌜Ty⌝ (icw-clo (⌜Mu⌝ TyD) ⊢⌜Ty⌝) ⊢⌜Ty⌝
   (iwf-ρ (ix (fst (var (vs vz))) (arrow (var vz) (snd (var (vs vz)))))
          (⊢ixP (⊢fstI (⊢var (there here)))
                (⊢arrow (⊢var here) (⊢sndI (⊢var (there here)))))
    (iwf-ρ (ix (fst (var (vs (vs vz)))) (var (vs vz)))
           (⊢ixP (⊢fstI (⊢var (there (there here)))) (⊢var (there here)))
     iwf-ι))

lamWf : IConWf I (Θ₀ I) ρ₀ x₀ lamC
lamWf =
  iwf-κ ⌜Ty⌝  (icw-clo (⌜Mu⌝ TyD)  ⊢⌜Ty⌝)  ⊢⌜Ty⌝
   (iwf-κ ⌜Ty⌝  (icw-clo (⌜Mu⌝ TyD)  ⊢⌜Ty⌝)  ⊢⌜Ty⌝
    (iwf-κ ⌜Cxt⌝ (icw-clo (⌜Mu⌝ CtxD) ⊢⌜Cxt⌝) ⊢⌜Cxt⌝
     (iwf-ρ (ix (consC (var (vs (vs vz))) (var vz)) (var (vs vz)))
            (⊢ixP (⊢consC (⊢var (there (there here))) (⊢var here))
                  (⊢var (there here)))
      (iwf-κ (⌜Id⌝ ⌜I⌝ (var (vs (vs (vs (vs vz)))))
                       (ix (var (vs vz))
                           (arrow (var (vs (vs (vs vz)))) (var (vs (vs vz))))))
             (icw-ford ⌜I⌝ _ _)
             (⊢⌜Id⌝ ⊢⌜I⌝ (⊢var (there (there (there (there here)))))
                    (⊢ixP (⊢var (there here))
                          (⊢arrow (⊢var (there (there (there here))))
                                  (⊢var (there (there here))))))
       iwf-ι))))

TmWf : IDescWf I TmD
TmWf = ty-El ⊢⌜I⌝ ,, idwf-cons appWf (idwf-cons lamWf idwf-nil)
