------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★★ GENERIC SCOPED SYNTAX WITH BINDING.
--
-- A syntax is a SIGNATURE: per sort, a list of constructor SHAPES, each a
-- list of fields
--
--     rec s k   a subterm of sort `s`, under `k` new binders
--     nat       a meta-level natural (an object `⌜Nat⌝`)
--     var       a variable of the ambient scope (a `Fin d`, `Lib/FinFam`)
--
-- and the syntax is the sorted, fibred family (`Lib/Sorted`, D075) over
-- `Σ (s : Fin ns) Nat` — sort and SCOPE DEPTH, the depth riding (D074).
-- Everything is defined ONCE, by recursion on shapes: the telescopes,
-- their well-formedness, the constructors (`⊢conSyn`) — and, in the
-- modules above this one, the fold, renaming and substitution.
--
-- ★ WHY.  The Knot is the kernel's own syntax.  Written row by row, each
--   operation cost one proof per constructor (the old Knot: 201 modules).
--   Here the Knot is one SIGNATURE, and every operation is a theorem
--   about all signatures.  (Allais–Atkey–Chapman–McBride–McKinna, "A type
--   and scope safe universe of syntaxes with binding", in this kernel.)
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Syn where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-pairʳ; ⟶*-nsuc; red→≅ᵀ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ; Lt; lt-z; lt-s )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.Sorted
open import DirectedHoTT.Lib.TelAt
open import DirectedHoTT.Lib.FinFam using ( FinD; ⊢FinD; FinI; ⊢isuc; toI )

private
  variable
    Γ Δ Θ : Cx
    c k n s : ℕ

------------------------------------------------------------------------
-- 1. SIGNATURES.
------------------------------------------------------------------------

data Fld : Set where
  rec : ℕ → ℕ → Fld      -- a subterm: its sort, and the binders it is under
  nat : Fld              -- a meta natural
  var : Fld              -- a variable of the ambient scope

infixr 5 _∷ʰ_ _∷ˢʰ_ _∷ᵍ_ _∷ᵒʰ_ _∷ᵒˢ_ _∷ᵒᵍ_
data Shape : Set where
  []ʰ  : Shape
  _∷ʰ_ : Fld → Shape → Shape

data Shapes : ℕ → Set where
  []ˢʰ  : Shapes zero
  _∷ˢʰ_ : Shape → Shapes c → Shapes (suc c)

data Sig : ℕ → Set where
  []ᵍ  : Sig zero
  _∷ᵍ_ : Shapes c → Sig n → Sig (suc n)

-- the shapes mention sorts in range
data FldOK (n : ℕ) : Fld → Set where
  ok-rec : Lt s n → FldOK n (rec s k)
  ok-nat : FldOK n nat
  ok-var : FldOK n var

data ShOK (n : ℕ) : Shape → Set where
  []ᵒʰ  : ShOK n []ʰ
  _∷ᵒʰ_ : {f : Fld} {sh : Shape} → FldOK n f → ShOK n sh → ShOK n (f ∷ʰ sh)

data ShsOK (n : ℕ) : Shapes c → Set where
  []ᵒˢ  : ShsOK n []ˢʰ
  _∷ᵒˢ_ : {sh : Shape} {shs : Shapes c} → ShOK n sh → ShsOK n shs → ShsOK n (sh ∷ˢʰ shs)

data SigOK (n : ℕ) : Sig k → Set where
  []ᵒᵍ  : SigOK n []ᵍ
  _∷ᵒᵍ_ : {shs : Shapes c} {sg : Sig k} → ShsOK n shs → SigOK n sg → SigOK n (shs ∷ᵍ sg)

-- constructor `k` of sort `s` has shape `sh`
data NthSh : Shapes c → ℕ → Shape → Set where
  nthʰ-z : {sh : Shape} {shs : Shapes c} → NthSh (sh ∷ˢʰ shs) zero sh
  nthʰ-s : {sh sh' : Shape} {shs : Shapes c} → NthSh shs k sh → NthSh (sh' ∷ˢʰ shs) (suc k) sh

data NthG : Sig n → ℕ → Shapes c → Set where
  nthᵍ-z : {shs : Shapes c} {sg : Sig n} → NthG (shs ∷ᵍ sg) zero shs
  nthᵍ-s : {shs : Shapes c} {shs' : Shapes k} {sg : Sig n} →
           NthG sg s shs → NthG (shs' ∷ᵍ sg) (suc s) shs

------------------------------------------------------------------------
-- 2. THE TELESCOPES — a shape read at an index TERM `i` (a field under
--    a σ-binder sees the index weakened).
------------------------------------------------------------------------

nsucs : ℕ → RTm Δ → RTm Δ
nsucs zero    t = t
nsucs (suc k) t = nsuc (nsucs k t)

nsucs-sub : (σ : Sub Δ Θ) (k : ℕ) (t : RTm Δ) → subTm σ (nsucs k t) ≡ nsucs k (subTm σ t)
nsucs-sub σ zero    t = refl
nsucs-sub σ (suc k) t = cong nsuc (nsucs-sub σ k t)

⟶*-nsucs : (k : ℕ) {t t' : RTm Δ} → t ⟶* t' → nsucs k t ⟶* nsucs k t'
⟶*-nsucs zero    r = r
⟶*-nsucs (suc k) r = ⟶*-nsuc (⟶*-nsucs k r)

⊢nsucs : {Γ : Ctx} (k : ℕ) {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ nsucs k t ∷ El ⌜Nat⌝
⊢nsucs zero    d = d
⊢nsucs (suc k) d = ⊢isuc (⊢nsucs k d)

-- a field's code, at an index
tel : Shape → RTm Δ → Tel Δ
tel []ʰ            i = tι
tel (rec s k ∷ʰ sh) i = tρ (pair (tag s) (nsucs k (snd i))) (tel sh i)
tel (nat ∷ʰ sh)     i = tσ ⌜Nat⌝ (tel sh (renTm vs i))
tel (var ∷ʰ sh)     i = tσ (⌜IMu⌝ ⌜Nat⌝ FinD (snd i)) (tel sh (renTm vs i))

tels : Shapes c → Tels (Δ ∙) c
tels []ˢʰ        = []ᵗ
tels (sh ∷ˢʰ shs) = tel sh (var vz) ∷ᵗ tels shs

stels : Sig n → STels (Δ ∙) n
stels []ᵍ        = []ˢᵗ
stels (shs ∷ᵍ sg) = tels shs ∷ˢᵗ stels sg

private
  tag-sub : (σ : Sub Δ Θ) (s : ℕ) → subTm σ (tag s) ≡ tag s
  tag-sub σ zero    = refl
  tag-sub σ (suc s) = cong fsuc (tag-sub σ s)

-- ★ a telescope instantiated IS the telescope at the instantiated index
sub-tel : (σ : Sub Δ Θ) (sh : Shape) (i : RTm Δ) → subTm σ ⌜ tel sh i ⌝ᵗ ≡ ⌜ tel sh (subTm σ i) ⌝ᵗ
sub-tel σ []ʰ            i = refl
sub-tel σ (rec s k ∷ʰ sh) i =
  cong₂ dρ (cong₂ pair (tag-sub σ s) (nsucs-sub σ k (snd i))) (sub-tel σ sh i)
sub-tel σ (nat ∷ʰ sh)     i =
  cong (λ X → dσ ⌜Nat⌝ (lam X)) (trans (sub-tel (extS σ) sh (renTm vs i)) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (wk-sub σ i)))
sub-tel σ (var ∷ʰ sh)     i =
  cong (λ X → dσ (⌜IMu⌝ ⌜Nat⌝ (subTm σ FinD) (snd (subTm σ i))) (lam X))
       (trans (sub-tel (extS σ) sh (renTm vs i)) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (wk-sub σ i)))

------------------------------------------------------------------------
-- 3. THE FAMILY.
------------------------------------------------------------------------

SI : ℕ → RTm Δ
SI n = SortI ⌜Nat⌝ n

⊢SI : {Γ : Ctx} → Γ ⊢ SI n ∷ U
⊢SI = ⊢SortI ⊢⌜Nat⌝

SD : Sig n → RTm Δ
SD sg = Dₛₜ (stels sg)

-- the syntax of sort `s` at depth `d`
SK : Sig n → ℕ → RTm Δ → RTy Δ
SK {n = n} sg s d = IMu (SI n) (SD sg) (pair (tag s) d)

-- the depth of an index
⊢depth : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El (SI n) → Γ ⊢ snd i ∷ El ⌜Nat⌝
⊢depth d = ⊢snd (unSortI d)

⊢ix : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Lt s n → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ pair (tag s) d ∷ El (SI n)
⊢ix lt dd = ⊢ixₛ ⊢⌜Nat⌝ lt dd

telOK : {Γ : Ctx} {sh : Shape} {i : RTm ⌊ Γ ⌋} →
        ShOK n sh → Γ ⊢ i ∷ El (SI n) → TelOK Γ (SI n) (tel sh i)
telOK []ᵒʰ                        di = ok-ι
telOK {sh = rec s k ∷ʰ _} (ok-rec lt ∷ᵒʰ ok) di = ok-ρ (⊢ix lt (⊢nsucs k (⊢depth di))) (telOK ok di)
telOK (ok-nat ∷ᵒʰ ok)             di = ok-σ ⊢⌜Nat⌝ (telOK ok (⊢wk di))
telOK (ok-var ∷ᵒʰ ok)             di = ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢depth di)) (telOK ok (⊢wk di))

telsOK : {Γ : Ctx} {shs : Shapes c} → ShsOK n shs → AllOK (Γ ▹ El (SI n)) (SI n) (tels shs)
telsOK []ᵒˢ         = []ᵒ
telsOK (ok ∷ᵒˢ oks) = telOK ok (⊢var here) ∷ᵒ telsOK oks

sigOK : {Γ : Ctx} {sg : Sig k} → SigOK n sg → AllSOK Γ (SI n) (stels sg)
sigOK []ᵒᵍ         = []ˢᵒ
sigOK (ok ∷ᵒᵍ oks) = telsOK ok ∷ˢᵒ sigOK oks

⊢SD : {Γ : Ctx} {sg : Sig n} → SigOK n sg → Γ ⊢ SD sg ∷ DescF (SI n)
⊢SD ok = ⊢Dₛₜ ⊢⌜Nat⌝ (sigOK ok)

------------------------------------------------------------------------
-- 4. ★ CONSTRUCTORS, generically: a payload is its fields, each typed.
------------------------------------------------------------------------

nth-tels : {shs : Shapes c} {sh : Shape} → NthSh shs k sh → NthT (tels {Δ = Δ} shs) k (tel sh (var vz))
nth-tels nthʰ-z     = nthᵗ-z
nth-tels (nthʰ-s n) = nthᵗ-s (nth-tels n)

nth-stels : {sg : Sig n} {shs : Shapes c} → NthG sg s shs → NthST (stels {Δ = Δ} sg) s (tels shs)
nth-stels nthᵍ-z     = nthˢᵗ-z
nth-stels (nthᵍ-s n) = nthˢᵗ-s (nth-stels n)

nthG-lt : {sg : Sig n} {shs : Shapes c} → NthG sg s shs → Lt s n
nthG-lt nthᵍ-z     = lt-z
nthG-lt (nthᵍ-s n) = lt-s (nthG-lt n)

nthG-ok : {sg : Sig k} {shs : Shapes c} → SigOK n sg → NthG sg s shs → ShsOK n shs
nthG-ok (ok ∷ᵒᵍ _)  nthᵍ-z     = ok
nthG-ok (_ ∷ᵒᵍ oks) (nthᵍ-s n) = nthG-ok oks n

nthSh-ok : {shs : Shapes c} {sh : Shape} → ShsOK n shs → NthSh shs k sh → ShOK n sh
nthSh-ok (ok ∷ᵒˢ _)  nthʰ-z     = ok
nthSh-ok (_ ∷ᵒˢ oks) (nthʰ-s n) = nthSh-ok oks n

-- the fields of a payload, at depth `d`, each typed
data Args (Γ : Ctx) (n : ℕ) (D d : RTm ⌊ Γ ⌋) : Shape → RTm ⌊ Γ ⌋ → Set where
  a[]   : Args Γ n D d []ʰ unit
  a-rec : {a p : RTm ⌊ Γ ⌋} {sh : Shape} →
          Γ ⊢ a ∷ IMu (SI n) D (pair (tag s) (nsucs k d)) → Args Γ n D d sh p →
          Args Γ n D d (rec s k ∷ʰ sh) (pair a p)
  a-nat : {a p : RTm ⌊ Γ ⌋} {sh : Shape} →
          Γ ⊢ a ∷ El ⌜Nat⌝ → Args Γ n D d sh p → Args Γ n D d (nat ∷ʰ sh) (pair a p)
  a-var : {a p : RTm ⌊ Γ ⌋} {sh : Shape} →
          Γ ⊢ a ∷ FinI d → Args Γ n D d sh p → Args Γ n D d (var ∷ʰ sh) (pair a p)

private
  ixConv : {Γ : Ctx} {I D t i i' : RTm ⌊ Γ ⌋} → i ⟶* i' → Γ ⊢ t ∷ IMu I D i' → Γ ⊢ t ∷ IMu I D i
  ixConv r d = ⊢conv d (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu r)))

  -- the rest of the telescope after a σ-field, instantiated: at the index again
  sub-rest : (a : RTm Δ) (sh : Shape) (i : RTm Δ) →
             subTm (single a) ⌜ tel sh (renTm vs i) ⌝ᵗ ≡ ⌜ tel sh i ⌝ᵗ
  sub-rest a sh i = trans (sub-tel (single a) sh (renTm vs i)) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (wk-cancel-tm a i))

-- ★ the payload, field by field, at ANY index whose depth reduces to `d`
⊢payArgs : {Γ : Ctx} {D i d p : RTm ⌊ Γ ⌋} {sh : Shape} →
           Γ ⊢ D ∷ DescF (SI n) → ShOK n sh → Γ ⊢ i ∷ El (SI n) → snd i ⟶* d →
           Args Γ n D d sh p → Γ ⊢ p ∷ El (dpay (SI n) D ⌜ tel sh i ⌝ᵗ)
⊢payArgs dD []ᵒʰ di r a[] = ⊢payι ⊢SI dD ⊢unit
⊢payArgs {sh = rec s k ∷ʰ sh} dD (ok-rec lt ∷ᵒʰ ok) di r (a-rec da as) =
  ⊢payρ ⊢SI dD (ok-ρ (⊢ix lt (⊢nsucs k (⊢depth di))) (telOK ok di))
        (ixConv (⟶*-pairʳ (⟶*-nsucs k r)) da) (⊢payArgs dD ok di r as)
⊢payArgs {D = D} {i = i} {sh = nat ∷ʰ sh} dD (ok-nat ∷ᵒʰ ok) di r (a-nat {a = a} {p = p} da as) =
  ⊢payσ ⊢SI dD (ok-σ ⊢⌜Nat⌝ (telOK ok (⊢wk di))) da
    (subst (λ X → _ ⊢ p ∷ El (dpay (SI _) D X)) (sym (sub-rest a sh i)) (⊢payArgs dD ok di r as))
⊢payArgs {Γ = Γ} {D = D} {i = i} {sh = var ∷ʰ sh} dD (ok-var ∷ᵒʰ ok) di r (a-var {a = a} {p = p} da as) =
  ⊢payσ ⊢SI dD (ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢depth di)) (telOK ok (⊢wk di)))
    (⊢conv da (csymᵀ (ctrnᵀ (credᵀ El-⌜IMu⌝) (red→≅ᵀ (⟶ᵀ*-IMu r)))))
    (subst (λ X → Γ ⊢ p ∷ El (dpay (SI _) D X)) (sym (sub-rest a sh i)) (⊢payArgs dD ok di r as))

-- ★★ CONSTRUCTOR `k` OF SORT `s`, at depth `d`
⊢conSyn : {Γ : Ctx} {sg : Sig n} {shs : Shapes c} {sh : Shape} {d p : RTm ⌊ Γ ⌋} →
          SigOK n sg → NthG sg s shs → NthSh shs k sh → Γ ⊢ d ∷ El ⌜Nat⌝ →
          Args Γ n (SD sg) d sh p → Γ ⊢ conₗ k p ∷ SK sg s d
⊢conSyn {n = n} {s = s} {Γ = Γ} {sg = sg} {shs = shs} {sh = sh} {d = d} {p = p} ok ng nh dd as =
  ⊢conₛₜ {Tss = stels sg} {Ts = tels shs} {T = tel sh (var vz)} ⊢⌜Nat⌝ (sigOK ok)
         (nth-stels ng) (nth-tels nh) dd
    (subst (λ X → Γ ⊢ p ∷ El (dpay (SI n) (SD sg) X)) (sym (sub-tel (single (pair (tag s) d)) sh (var vz)))
           (⊢payArgs (⊢SD ok) (nthSh-ok (nthG-ok ok ng) nh) (⊢ix (nthG-lt ng) dd) (step (βsnd _ _) done) as))
