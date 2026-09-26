------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ A FAMILY INDEXED BY A PAIR.
--
--        K : (sort, depth) → Set
--
--        kbase :                        K (0, d)      -- a TYPE
--        kvar  :                        K (1, d)      -- a TERM
--        klam  : K (1, suc d)         → K (1, d)      -- DEPTH shifts
--        kann  : K (1, d) → K (0, d)  → K (1, d)      -- SORT crosses
--
-- ★ WHY THIS FILE EXISTS.  The real `RTm` knot's index is a sort tag AND
--   a context depth, and `RTy`-at-the-same-depth is a function of the
--   ambient index in one component while the other is held fixed.  Every
--   other example is indexed by `⌜Nat⌝`; this one's index CODE is
--   `⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝` (D073: the index is a code in Γ).
--
-- ★★ D074 (fibred descriptions) + FORD THE COMPONENT, NOT THE PAIR.  Each
--   constructor telescope sees the index `i` it lands at.  The DEPTH is
--   an input — `klam`'s field is simply at `(1, suc (snd i))` — so it
--   rides with no equation.  The SORT is a computed target (a constant),
--   so each constructor fords it: one `⌜Id⌝ ⌜Nat⌝ (fst i) s` field.
--   Fording the whole pair would pin the depth, which must stay free.
--
-- ⚠ WHAT THIS COSTS: `fst`/`snd` are term formers that step by
--   `βfst`/`βsnd`, so at a concrete index `pair t d` the payload still
--   reads `fst (pair t d)`, and each such spot is one explicit
--   conversion (`fordAt`, `ixConv`).  A chain-length cost, not a typing
--   one — and the fold (§4) never pays it: `fold-ι` is index-generic.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.PairIx where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Lib.Sugar using ( conₗ; methₗ; Dₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelFold using ( sizeAlg; foldMs; ⊢foldE; fold-ι )

------------------------------------------------------------------------
-- 0. The index CODE: a pair of naturals.
------------------------------------------------------------------------

IP : {Γ : Cx} → RTm Γ
IP = ⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝

⊢IP : {Γ : Ctx} → Γ ⊢ IP ∷ U
⊢IP = ⊢⌜Σ⌝ ⊢⌜Nat⌝ ⊢⌜Nat⌝

sTy sTm : {Γ : Cx} → RTm Γ
sTy = nzero
sTm = nsuc nzero

-- the ambient index, at one binder
ix : {Γ : Cx} → RTm (Γ ∙)
ix = var vz

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

⊢s1 : {Γ : Ctx} → Γ ⊢ nsuc nzero ∷ El ⌜Nat⌝
⊢s1 = toI (⊢nsuc ⊢nzero)

⊢sTy : {Γ : Ctx} → Γ ⊢ sTy ∷ El ⌜Nat⌝
⊢sTy = toI ⊢nzero

⊢isuc : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ nsuc t ∷ El ⌜Nat⌝
⊢isuc d = toI (⊢nsuc (fromI d))

-- ★ the index's components: with a CODE index they come out at
--   `El ⌜Nat⌝` directly — the index type needs no bridge to `Nat`.
unP : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IP → Γ ⊢ i ∷ Σ' (El ⌜Nat⌝) (El ⌜Nat⌝)
unP d = ⊢conv d (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝))

⊢π₁ : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IP → Γ ⊢ fst i ∷ El ⌜Nat⌝
⊢π₁ d = ⊢fst (unP d)

⊢π₂ : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IP → Γ ⊢ snd i ∷ El ⌜Nat⌝
⊢π₂ d = ⊢snd (unP d)

⊢ixP : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ b ∷ El ⌜Nat⌝ → Γ ⊢ pair a b ∷ El IP
⊢ixP da db = ⊢conv (⊢pair (ty-El ⊢⌜Nat⌝) da db) (csymᵀ (credᵀ (El-⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝)))

⊢Eq : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ b ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Id⌝ ⌜Nat⌝ a b ∷ U
⊢Eq = ⊢⌜Id⌝ ⊢⌜Nat⌝

------------------------------------------------------------------------
-- 1. THE DESCRIPTION — telescopes over the index `i` (`var vz`).
--
-- ⚠ READ THE INDICES.  `klam`'s field is at `(1, suc (snd i))` — SAME
--   sort, depth PUSHED.  `kann`'s second field is at `(0, snd i)` —
--   OTHER sort, depth HELD.  `tρ` binds nothing, so `ix` is the index
--   throughout; only the sort ford is a field.
------------------------------------------------------------------------

sortIs : {Γ : Cx} → RTm (Γ ∙) → Tel (Γ ∙)
sortIs s = tσ (⌜Id⌝ ⌜Nat⌝ (fst ix) s) tι

kbaseT kvarT klamT kannT : {Γ : Cx} → Tel (Γ ∙)
kbaseT = sortIs sTy
kvarT  = sortIs sTm
klamT  = tρ (pair sTm (nsuc (snd ix))) (sortIs sTm)
kannT  = tρ (pair sTm (snd ix)) (tρ (pair sTy (snd ix)) (sortIs sTm))

KTs : {Γ : Cx} → Tels (Γ ∙) 4
KTs = kbaseT ∷ᵗ kvarT ∷ᵗ klamT ∷ᵗ kannT ∷ᵗ []ᵗ

KD : {Γ : Cx} → RTm Γ
KD = Dₗ ⌜ KTs ⌝ₛ

K : {Γ : Cx} → RTm Γ → RTy Γ
K i = IMu IP KD i

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.
------------------------------------------------------------------------

sortOK : {Γ : Ctx} {i s : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IP → Γ ⊢ s ∷ El ⌜Nat⌝ →
         TelOK Γ IP (tσ (⌜Id⌝ ⌜Nat⌝ (fst i) s) tι)
sortOK di ds = ok-σ (⊢Eq (⊢π₁ di) ds) ok-ι

module _ {Γ : Ctx} where
  private
    Γ₁ = Γ ▹ El IP
    v : Γ₁ ⊢ ix ∷ El IP
    v = ⊢var here

  kbaseOK : TelOK Γ₁ IP kbaseT
  kbaseOK = sortOK v ⊢sTy

  kvarOK : TelOK Γ₁ IP kvarT
  kvarOK = sortOK v ⊢s1

  -- ★★★ the binder row: depth PUSHED
  klamOK : TelOK Γ₁ IP klamT
  klamOK = ok-ρ (⊢ixP ⊢s1 (⊢isuc (⊢π₂ v))) (sortOK v ⊢s1)

  -- ★★★ the cross-sort row: sort CHANGES, depth HELD
  kannOK : TelOK Γ₁ IP kannT
  kannOK = ok-ρ (⊢ixP ⊢s1 (⊢π₂ v)) (ok-ρ (⊢ixP ⊢sTy (⊢π₂ v)) (sortOK v ⊢s1))

KOK : {Γ : Ctx} → AllOK (Γ ▹ El IP) IP KTs
KOK = kbaseOK ∷ᵒ kvarOK ∷ᵒ klamOK ∷ᵒ kannOK ∷ᵒ []ᵒ

⊢KD : {Γ : Ctx} → Γ ⊢ KD ∷ DescF IP
⊢KD = ⊢Dₜ ⊢IP KOK

------------------------------------------------------------------------
-- 3. INHABITATION — at EVERY depth.
--
-- A description can be well-formed and still have no inhabitant
-- (`Examples/Vec.no-cons-at-zero`), so §2 alone would say only that the
-- judgement accepts a pair index.  Below, the four constructors inhabit
-- `K (s, d)` at an arbitrary depth `d`.
--
-- ⚠ THIS IS WHERE THE PROJECTIONS GET PAID FOR: the payload reads
--   `fst (pair t d)` / `snd (pair t d)`, one explicit conversion each.
------------------------------------------------------------------------

-- the sort ford at a concrete index: `fst (pair t d)` must first STEP
fordAt : {Γ : Ctx} {t d : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ t ∷ El (⌜Id⌝ ⌜Nat⌝ (fst (pair t d)) t)
fordAt {t = t} {d = d} dt =
  ⊢conv (⊢idrefl ⊢⌜Nat⌝ dt)
    (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βfst t d)))) (credᵀ (El-⌜Id⌝ ⌜Nat⌝ t t))))

-- convert along a reduction OF THE INDEX
ixConv : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} → i ⟶ i' → Γ ⊢ t ∷ K i' → Γ ⊢ t ∷ K i
ixConv r d = ⊢conv d (csymᵀ (credᵀ (ξ-IMuⁱ r)))

kbase kvar : {Γ : Cx} → RTm Γ
kbase = conₗ zero (pair (idrefl ⌜Nat⌝ sTy) unit)
kvar  = conₗ (suc zero) (pair (idrefl ⌜Nat⌝ sTm) unit)

klam : {Γ : Cx} → RTm Γ → RTm Γ
klam b = conₗ (suc (suc zero)) (pair b (pair (idrefl ⌜Nat⌝ sTm) unit))

kann : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kann t a = conₗ (suc (suc (suc zero))) (pair t (pair a (pair (idrefl ⌜Nat⌝ sTm) unit)))

module _ {Γ : Ctx} {d : RTm ⌊ Γ ⌋} (dd : Γ ⊢ d ∷ El ⌜Nat⌝) where
  private
    dTy = ⊢ixP ⊢sTy dd
    dTm = ⊢ixP ⊢s1 dd
    -- the tail every constructor ends with: the sort ford, then `unit`
    ford : {s : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ El ⌜Nat⌝ →
           Γ ⊢ pair (idrefl ⌜Nat⌝ s) unit ∷ El (dpay IP KD ⌜ tσ (⌜Id⌝ ⌜Nat⌝ (fst (pair s d)) s) tι ⌝ᵗ)
    ford ds = ⊢payσ ⊢IP ⊢KD (sortOK (⊢ixP ds dd) ds) (fordAt ds) (⊢payι ⊢IP ⊢KD ⊢unit)

  ⊢kbase : Γ ⊢ kbase ∷ K (pair sTy d)
  ⊢kbase = ⊢conₜ ⊢IP KOK nthᵗ-z dTy (ford ⊢sTy)

  ⊢kvar : Γ ⊢ kvar ∷ K (pair sTm d)
  ⊢kvar = ⊢conₜ ⊢IP KOK (nthᵗ-s nthᵗ-z) dTm (ford ⊢s1)

  -- ★★★ THE BINDER: the field's index `pair 1 (suc (snd (pair 1 d)))`
  --   — the ambient's second component, pushed.
  ⊢klam : {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ K (pair sTm (nsuc d)) → Γ ⊢ klam b ∷ K (pair sTm d)
  ⊢klam db =
    ⊢conₜ ⊢IP KOK (nthᵗ-s (nthᵗ-s nthᵗ-z)) dTm
      (⊢payρ ⊢IP ⊢KD (ok-ρ (⊢ixP ⊢s1 (⊢isuc (⊢π₂ dTm))) (sortOK dTm ⊢s1))
             (ixConv (ξ-pairʳ (ξ-nsuc (βsnd sTm d))) db) (ford ⊢s1))

  -- ★★★ THE CROSS-SORT CONSTRUCTOR: both fields convert through the
  --   SAME `βsnd`.
  ⊢kann : {t a : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ K (pair sTm d) → Γ ⊢ a ∷ K (pair sTy d) →
          Γ ⊢ kann t a ∷ K (pair sTm d)
  ⊢kann dt da =
    ⊢conₜ ⊢IP KOK (nthᵗ-s (nthᵗ-s (nthᵗ-s nthᵗ-z))) dTm
      (⊢payρ ⊢IP ⊢KD (ok-ρ (⊢ixP ⊢s1 (⊢π₂ dTm)) okA)
             (ixConv (ξ-pairʳ (βsnd sTm d)) dt)
        (⊢payρ ⊢IP ⊢KD okA (ixConv (ξ-pairʳ (βsnd sTm d)) da) (ford ⊢s1)))
    where okA = ok-ρ (⊢ixP ⊢sTy (⊢π₂ dTm)) (sortOK dTm ⊢s1)

-- `ann (λ. var) base` — a term that uses the binder AND both sorts.
kterm : {Γ : Cx} → RTm Γ
kterm = kann (klam kvar) kbase

⊢kterm : ◇ ⊢ kterm ∷ K (pair sTm nzero)
⊢kterm = ⊢kann z (⊢klam z (⊢kvar (⊢isuc z))) (⊢kbase z)
  where z = toI ⊢nzero

------------------------------------------------------------------------
-- 4. AND `ielim` WORKS THERE.  `size : K i → Nat` is the library FOLD
--    (`Lib/TelFold.sizeAlg`); the method tuple is computed from the
--    telescopes, with the index binder at `El IP`.
------------------------------------------------------------------------

msize : {Γ : Cx} → RTm Γ
msize = methₗ (foldMs sizeAlg KTs)

size : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
size i t = ielim KD i msize t

⊢size : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El IP → Γ ⊢ t ∷ K i → Γ ⊢ size i t ∷ Nat
⊢size di dt = ⊢ielim ⊢IP ⊢KD ty-Nat (⊢foldE sizeAlg ⊢IP KOK) di dt

-- …and it FIRES at a pair index: a leaf…
size-var : {Γ : Cx} {i : RTm Γ} → size i kvar ⟶* nsuc nzero
size-var = fold-ι sizeAlg {Ts = KTs} (nthᵗ-s nthᵗ-z)

-- ★★ …and under the binder, where the IH runs at the PUSHED index
--   `(1, suc (snd i))` — which the fold never needs reduced.
size-lam : {Γ : Cx} {i : RTm Γ} → size i (klam kvar) ⟶* nsuc (nsuc nzero)
size-lam =
  ⟶*-trans (fold-ι sizeAlg {Ts = KTs} (nthᵗ-s (nthᵗ-s nthᵗ-z)))
    (⟶*-nsuc (step (βfst _ _) (step (ξ-ielimᵗ (βfst _ _)) size-var)))
