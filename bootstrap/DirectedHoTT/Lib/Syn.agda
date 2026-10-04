-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★★ GENERIC SCOPED SYNTAX WITH BINDING.
--
-- A syntax is a SIGNATURE: per sort, a list of constructor SHAPES, each a
-- list of fields
--
--     rec s k   a subterm of sort `s`, under `k` new binders
--     nat       a meta-level natural (an object `⌜Nat⌝`)
--     cls s     a CLOSED subterm of sort `s` — at depth 0 in any scope (a
--               definition's body); renaming and substitution copy it
--
-- and one distinguished shape `vʰ`, THE VARIABLE: a `Fin d` of the
-- ambient scope (`Lib/FinFam`).  Variables are a shape, not a field kind,
-- because substitution replaces the whole node (Allais et al.'s `'var`).
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
open import Agda.Builtin.Unit using ( ⊤ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-pairʳ; ⟶*-nsuc; red→≅ᵀ; ⟶ᵀ*-IMu; _⟶ᵀ*_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Lib.Sugar using ( tag; conₗ; Lt; lt-z; lt-s; Cons; []; _∷_; subC; sel; selF; sel-sub; selF-sub; Dσ; Dσ-sub )
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
  cls : ℕ → Fld          -- ★ a CLOSED subterm of a sort: at depth 0, whatever
                         --   the scope (a definition's body); traversals copy it

infixr 5 _∷ʰ_ _∷ˢʰ_ _∷ᵍ_ _∷ᶠ_ _∷ᵒˢ_ _∷ᵒᵍ_
data Shape : Set where
  []ʰ  : Shape
  _∷ʰ_ : Fld → Shape → Shape
  vʰ   : Shape            -- ★ the variable constructor

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
  ok-cls : Lt s n → FldOK n (cls s)

-- a FIELDS shape, well-formed
data FOK (n : ℕ) : Shape → Set where
  []ᶠ  : FOK n []ʰ
  _∷ᶠ_ : {f : Fld} {sh : Shape} → FldOK n f → FOK n sh → FOK n (f ∷ʰ sh)

-- ★ a well-formed shape: fields, or the variable ALONE (`f ∷ʰ vʰ` is not
--   a constructor of any syntax)
data ShOK (n : ℕ) : Shape → Set where
  fᵒʰ : {sh : Shape} → FOK n sh → ShOK n sh
  vᵒʰ : ShOK n vʰ

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

-- ★ a POSITION BY ITS NUMBER: `atʰ 13`, `atᵍ 1` — the proof is computed and
--   the range checked (`InSh`/`InG` compute to ⊤, which Agda fills in by
--   eta, or to the empty type).  A use site says which constructor, not how
--   to reach it.
private
  data Out : Set where

shAt : Shapes c → ℕ → Shape
shAt []ˢʰ         k       = []ʰ
shAt (sh ∷ˢʰ shs) zero    = sh
shAt (sh ∷ˢʰ shs) (suc k) = shAt shs k

InSh : Shapes c → ℕ → Set
InSh []ˢʰ         k       = Out
InSh (sh ∷ˢʰ shs) zero    = ⊤
InSh (sh ∷ˢʰ shs) (suc k) = InSh shs k

atʰ : {shs : Shapes c} (k : ℕ) {_ : InSh shs k} → NthSh shs k (shAt shs k)
atʰ {shs = []ˢʰ}         k {()}
atʰ {shs = sh ∷ˢʰ shs} zero    = nthʰ-z
atʰ {shs = sh ∷ˢʰ shs} (suc k) {i} = nthʰ-s (atʰ k {i})

cAt : Sig n → ℕ → ℕ
cAt []ᵍ                     s       = zero
cAt (_∷ᵍ_ {c = c} shs sg)  zero    = c
cAt (shs ∷ᵍ sg)             (suc s) = cAt sg s

sigAt : (sg : Sig n) (s : ℕ) → Shapes (cAt sg s)
sigAt []ᵍ          s       = []ˢʰ
sigAt (shs ∷ᵍ sg)  zero    = shs
sigAt (shs ∷ᵍ sg)  (suc s) = sigAt sg s

InG : Sig n → ℕ → Set
InG []ᵍ          s       = Out
InG (shs ∷ᵍ sg)  zero    = ⊤
InG (shs ∷ᵍ sg)  (suc s) = InG sg s

atᵍ : {sg : Sig n} (s : ℕ) {_ : InG sg s} → NthG sg s (sigAt sg s)
atᵍ {sg = []ᵍ}        s {()}
atᵍ {sg = shs ∷ᵍ sg} zero    = nthᵍ-z
atᵍ {sg = shs ∷ᵍ sg} (suc s) {i} = nthᵍ-s (atᵍ s {i})

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
tel (cls s ∷ʰ sh)   i = tρ (pair (tag s) nzero) (tel sh i)
tel vʰ              i = tσ (⌜IMu⌝ ⌜Nat⌝ FinD (snd i)) tι

tels : Shapes c → Tels (Δ ∙) c
tels []ˢʰ        = []ᵗ
tels (sh ∷ˢʰ shs) = tel sh (var vz) ∷ᵗ tels shs

stels : Sig n → STels (Δ ∙) n
stels []ᵍ        = []ˢᵗ
stels (shs ∷ᵍ sg) = tels shs ∷ˢᵗ stels sg

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
sub-tel σ (cls s ∷ʰ sh)   i = cong₂ dρ (cong₂ pair (tag-sub σ s) refl) (sub-tel σ sh i)
sub-tel σ vʰ              i = refl

------------------------------------------------------------------------
-- 3. THE FAMILY.
------------------------------------------------------------------------

SI : ℕ → RTm Δ
SI n = SortI ⌜Nat⌝ n

⊢SI : {Γ : Ctx} → Γ ⊢ SI n ∷ U
⊢SI = ⊢SortI ⊢⌜Nat⌝

SI-ren : {Θ : Cx} (ρ : Ren Δ Θ) (n : ℕ) → renTm ρ (SI n) ≡ SI n
SI-ren ρ n = SortI-ren ρ ⌜Nat⌝ n

SI-sub : {Θ : Cx} (σ : Sub Δ Θ) (n : ℕ) → subTm σ (SI n) ≡ SI n
SI-sub σ n = SortI-sub σ ⌜Nat⌝ n

-- the family's inductive type commutes with substitution, the arity included
IMuSI-sub : {Θ : Cx} (σ : Sub Δ Θ) (D j : RTm Δ) → subTy σ (IMu (SI n) D j) ≡ IMu (SI n) (subTm σ D) (subTm σ j)
IMuSI-sub {n = n} σ D j = cong (λ I → IMu I (subTm σ D) (subTm σ j)) (SI-sub σ n)

IMuSI-ren : {Θ : Cx} (ρ : Ren Δ Θ) (D j : RTm Δ) → renTy ρ (IMu (SI n) D j) ≡ IMu (SI n) (renTm ρ D) (renTm ρ j)
IMuSI-ren {n = n} ρ D j = cong (λ I → IMu I (renTm ρ D) (renTm ρ j)) (SI-ren ρ n)

-- `k` binders further out
_⁺_ : Cx → ℕ → Cx
Δ ⁺ zero  = Δ
Δ ⁺ suc k = (Δ ⁺ k) ∙

wks : (k : ℕ) → RTm Δ → RTm (Δ ⁺ k)
wks zero    t = t
wks (suc k) t = renTm vs (wks k t)

SI-wks : (k : ℕ) → wks {Δ = Δ} k (SI n) ≡ SI n
SI-wks zero            = refl
SI-wks {n = n} (suc k) = trans (cong (renTm vs) (SI-wks k)) (SI-ren vs n)

-- a variable at the family: its stored type is `SI n` under `k` weakenings,
--   at the call site `⊢varSI x (SI-wks k)`
⊢varSI : {Γ : Ctx} {x : Var ⌊ Γ ⌋} {X : RTm ⌊ Γ ⌋} → Γ ∋ x ∷ El X → X ≡ SI n → Γ ⊢ var x ∷ El (SI n)
⊢varSI x e = ⊢-cast (cong El e) (⊢var x)

-- weakening an index of `SI n` — the numeral arity does not compute under `vs`
⊢wkSI : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El (SI n) → (Γ ▹ A) ⊢ renTm vs i ∷ El (SI n)
⊢wkSI {n = n} di = ⊢-cast (cong El (SI-ren vs n)) (⊢wk di)

⊢wkDSI : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {D : RTm ⌊ Γ ⌋} → Γ ⊢ D ∷ DescF (SI n) → (Γ ▹ B) ⊢ renTm vs D ∷ DescF (SI n)
⊢wkDSI {n = n} {Γ = Γ} {B = B} {D = D} dD =
  subst (λ X → (Γ ▹ B) ⊢ renTm vs D ∷ DescF X) (SI-ren vs n) (⊢wkD dD)
  where open import DirectedHoTT.Metatheory.Premises using ( ⊢wkD )

⊢wkDescSI : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {C : RTm ⌊ Γ ⌋} → Γ ⊢ C ∷ Desc (SI n) → (Γ ▹ B) ⊢ renTm vs C ∷ Desc (SI n)
⊢wkDescSI {n = n} dC = ⊢-cast (cong Desc (SI-ren vs n)) (⊢wk dC)

-- a motive context over a renamed `SI n`
motSI : {Γ : Ctx} {X D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} → X ≡ SI n → motCtx Γ X D ⊢ty M → motCtx Γ (SI n) D ⊢ty M
motSI {n = n} {Γ = Γ} {D = D} {M = M} e d = subst (λ X → motCtx Γ X D ⊢ty M) e d

-- `ok-σ` at a family `SI n`, cast back to the renamed index
ok-σSI : {Γ : Ctx} {S : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} →
         Γ ⊢ S ∷ U → TelOK (Γ ▹ El S) (SI n) T → TelOK Γ (SI n) (tσ S T)
ok-σSI {n = n} {Γ = Γ} {S = S} {T = T} dS ok =
  ok-σ dS (subst (λ X → TelOK (Γ ▹ El S) X T) (sym (SI-ren vs n)) ok)

SD : Sig n → RTm Δ
SD sg = Dₛₜ (stels sg)

-- the syntax of sort `s` at depth `d` — OPAQUE: it carries the whole
--   description, and two syntactic forms of one context (a telescope's
--   `⌊ Ξ ⌋ ∙`, a typing's `⌊ Ξ ▹ A ⌋`) would otherwise compare it by
--   normalising every constructor (`context-form-mismatch-opaque`; the
--   Knot's tr row: 104.8 s → 43.3 s).  Its interface: `SK-def`, `SK-sub`,
--   and the constructor typings `⊢conSyn`/`⊢conV`.
opaque
  SK : Sig n → ℕ → RTm Δ → RTy Δ
  SK {n = n} sg s d = IMu (SI n) (SD sg) (pair (tag s) d)

  SK-def : {sg : Sig n} {s : ℕ} {d : RTm Δ} → SK sg s d ≡ IMu (SI n) (SD sg) (pair (tag s) d)
  SK-def = refl

-- the escape hatch at the typing level: an eliminator sees the `IMu`
⊢SK→IMu : {Γ : Ctx} {sg : Sig n} {s : ℕ} {d t : RTm ⌊ Γ ⌋} →
          Γ ⊢ t ∷ SK sg s d → Γ ⊢ t ∷ IMu (SI n) (SD sg) (pair (tag s) d)
⊢SK→IMu {sg = sg} {s} {d} = ⊢-cast (SK-def {sg = sg} {s = s} {d = d})

⊢IMu→SK : {Γ : Ctx} {sg : Sig n} {s : ℕ} {d t : RTm ⌊ Γ ⌋} →
          Γ ⊢ t ∷ IMu (SI n) (SD sg) (pair (tag s) d) → Γ ⊢ t ∷ SK sg s d
⊢IMu→SK {sg = sg} {s} {d} = ⊢-cast (sym (SK-def {sg = sg} {s = s} {d = d}))

-- the depth reduces under the sort
opaque
  unfolding SK
  ξ-SK : {sg : Sig n} {s : ℕ} {d d' : RTm Δ} → d ⟶ d' → SK sg s d ⟶ᵀ SK sg s d'
  ξ-SK r = ξ-IMuⁱ (ξ-pairʳ r)

  ⟶ᵀ*-SK : {sg : Sig n} {s : ℕ} {d d' : RTm Δ} → d ⟶* d' → SK sg s d ⟶ᵀ* SK sg s d'
  ⟶ᵀ*-SK r = ⟶ᵀ*-IMu (⟶*-pairʳ r)

  -- the quoted sort decodes to the sort
  El-⌜SK⌝ : {sg : Sig n} {s : ℕ} {d : RTm Δ} → El (⌜IMu⌝ (SI n) (SD sg) (pair (tag s) d)) ⟶ᵀ SK sg s d
  El-⌜SK⌝ = El-⌜IMu⌝

-- the depth of an index
⊢depth : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El (SI n) → Γ ⊢ snd i ∷ El ⌜Nat⌝
⊢depth d = ⊢snd (unSortI d)

⊢ix : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Lt s n → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ pair (tag s) d ∷ El (SI n)
⊢ix lt dd = ⊢ixₛ ⊢⌜Nat⌝ lt dd

telOKf : {Γ : Ctx} {sh : Shape} {i : RTm ⌊ Γ ⌋} →
         FOK n sh → Γ ⊢ i ∷ El (SI n) → TelOK Γ (SI n) (tel sh i)
telOKf []ᶠ                        di = ok-ι
telOKf {sh = rec s k ∷ʰ _} (ok-rec lt ∷ᶠ ok) di = ok-ρ (⊢ix lt (⊢nsucs k (⊢depth di))) (telOKf ok di)
telOKf (ok-nat ∷ᶠ ok)             di = ok-σSI ⊢⌜Nat⌝ (telOKf ok (⊢wkSI di))
telOKf (ok-cls lt ∷ᶠ ok)          di = ok-ρ (⊢ix lt (toI ⊢nzero)) (telOKf ok di)

telOK : {Γ : Ctx} {sh : Shape} {i : RTm ⌊ Γ ⌋} →
        ShOK n sh → Γ ⊢ i ∷ El (SI n) → TelOK Γ (SI n) (tel sh i)
telOK (fᵒʰ ok) di = telOKf ok di
telOK vᵒʰ      di = ok-σSI (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢depth di)) ok-ι

telsOK : {Γ : Ctx} {shs : Shapes c} → ShsOK n shs → AllOK (Γ ▹ El (SI n)) (SI n) (tels shs)
telsOK []ᵒˢ         = []ᵒ
telsOK {n = n} (ok ∷ᵒˢ oks) = telOK ok (⊢-cast (cong El (SI-ren vs n)) (⊢var here)) ∷ᵒ telsOK oks

sigOK : {Γ : Ctx} {sg : Sig k} → SigOK n sg → AllSOK Γ (SI n) (stels sg)
sigOK []ᵒᵍ         = []ˢᵒ
sigOK {n = n} {Γ = Γ} (_∷ᵒᵍ_ {shs = shs} ok oks) =
  subst (λ X → AllOK (Γ ▹ El (SI n)) X (tels shs)) (sym (SI-ren vs n)) (telsOK ok) ∷ˢᵒ sigOK oks

⊢SD : {Γ : Ctx} {sg : Sig n} → SigOK n sg → Γ ⊢ SD sg ∷ DescF (SI n)
⊢SD ok = ⊢Dₛₜ ⊢⌜Nat⌝ (sigOK ok)

-- a sort of the signature is a type
ty-SK : {Γ : Ctx} {sg : Sig n} {d : RTm ⌊ Γ ⌋} → SigOK n sg → Lt s n → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ty SK sg s d
ty-SK {Γ = Γ} {sg = sg} {d = d} ok lt dd =
  subst (Γ ⊢ty_) (sym (SK-def {sg = sg} {s = _} {d = d})) (ty-IMu ⊢SI (⊢SD ok) (⊢ix lt dd))

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

-- the fields of a payload of signature `sg`, at depth `d`, each typed — a
--   recursive field is a term of the signature's sort (`SK`, opaque)
data Args (Γ : Ctx) (n : ℕ) (sg : Sig n) (d : RTm ⌊ Γ ⌋) : Shape → RTm ⌊ Γ ⌋ → Set where
  a[]   : Args Γ n sg d []ʰ unit
  a-rec : {a p : RTm ⌊ Γ ⌋} {sh : Shape} →
          Γ ⊢ a ∷ SK sg s (nsucs k d) → Args Γ n sg d sh p →
          Args Γ n sg d (rec s k ∷ʰ sh) (pair a p)
  a-nat : {a p : RTm ⌊ Γ ⌋} {sh : Shape} →
          Γ ⊢ a ∷ El ⌜Nat⌝ → Args Γ n sg d sh p → Args Γ n sg d (nat ∷ʰ sh) (pair a p)
  a-cls : {a p : RTm ⌊ Γ ⌋} {sh : Shape} →
          Γ ⊢ a ∷ SK sg s nzero → Args Γ n sg d sh p →
          Args Γ n sg d (cls s ∷ʰ sh) (pair a p)
  a-v   : {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ FinI d → Args Γ n sg d vʰ (pair a unit)

private
  ixConv : {Γ : Ctx} {I D t i i' : RTm ⌊ Γ ⌋} → i ⟶* i' → Γ ⊢ t ∷ IMu I D i' → Γ ⊢ t ∷ IMu I D i
  ixConv r d = ⊢conv d (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu r)))

  -- the rest of the telescope after a σ-field, instantiated: at the index again
  sub-rest : (a : RTm Δ) (sh : Shape) (i : RTm Δ) →
             subTm (single a) ⌜ tel sh (renTm vs i) ⌝ᵗ ≡ ⌜ tel sh i ⌝ᵗ
  sub-rest a sh i = trans (sub-tel (single a) sh (renTm vs i)) (cong (λ z → ⌜ tel sh z ⌝ᵗ) (wk-cancel-tm a i))

-- ★ the payload, field by field, at ANY index whose depth reduces to `d`
⊢payArgsF : {Γ : Ctx} {sg : Sig n} {i d p : RTm ⌊ Γ ⌋} {sh : Shape} →
            Γ ⊢ SD sg ∷ DescF (SI n) → FOK n sh → Γ ⊢ i ∷ El (SI n) → snd i ⟶* d →
            Args Γ n sg d sh p → Γ ⊢ p ∷ El (dpay (SI n) (SD sg) ⌜ tel sh i ⌝ᵗ)
⊢payArgsF dD []ᶠ di r a[] = ⊢payι ⊢SI dD ⊢unit
⊢payArgsF {sg = sg} {d = d} {sh = rec s k ∷ʰ sh} dD (ok-rec lt ∷ᶠ ok) di r (a-rec da as) =
  ⊢payρ ⊢SI dD (ok-ρ (⊢ix lt (⊢nsucs k (⊢depth di))) (telOKf ok di))
        (ixConv (⟶*-pairʳ (⟶*-nsucs k r)) (⊢SK→IMu {sg = sg} {s = s} {d = nsucs k d} da)) (⊢payArgsF dD ok di r as)
⊢payArgsF {sg = sg} {sh = cls s ∷ʰ sh} dD (ok-cls lt ∷ᶠ ok) di r (a-cls da as) =
  ⊢payρ ⊢SI dD (ok-ρ (⊢ix lt (toI ⊢nzero)) (telOKf ok di))
        (⊢SK→IMu {sg = sg} {s = s} {d = nzero} da) (⊢payArgsF dD ok di r as)
⊢payArgsF {sg = sg} {i = i} {sh = nat ∷ʰ sh} dD (ok-nat ∷ᶠ ok) di r (a-nat {a = a} {p = p} da as) =
  ⊢payσ ⊢SI dD (ok-σSI ⊢⌜Nat⌝ (telOKf ok (⊢wkSI di))) da
    (subst (λ X → _ ⊢ p ∷ El (dpay (SI _) (SD sg) X)) (sym (sub-rest a sh i)) (⊢payArgsF dD ok di r as))

⊢payArgs : {Γ : Ctx} {sg : Sig n} {i d p : RTm ⌊ Γ ⌋} {sh : Shape} →
           Γ ⊢ SD sg ∷ DescF (SI n) → ShOK n sh → Γ ⊢ i ∷ El (SI n) → snd i ⟶* d →
           Args Γ n sg d sh p → Γ ⊢ p ∷ El (dpay (SI n) (SD sg) ⌜ tel sh i ⌝ᵗ)
⊢payArgs dD (fᵒʰ ok) di r as = ⊢payArgsF dD ok di r as
⊢payArgs {Γ = Γ} {i = i} {sh = vʰ} dD vᵒʰ di r (a-v {a = a} da) =
  ⊢payσ ⊢SI dD (ok-σSI (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢depth di)) ok-ι)
    (⊢conv da (csymᵀ (ctrnᵀ (credᵀ El-⌜IMu⌝) (red→≅ᵀ (⟶ᵀ*-IMu r)))))
    (⊢payι ⊢SI dD ⊢unit)

-- ★★ CONSTRUCTOR `k` OF SORT `s`, at depth `d`
opaque
  unfolding SK
  ⊢conSyn : {Γ : Ctx} {sg : Sig n} {shs : Shapes c} {sh : Shape} {d p : RTm ⌊ Γ ⌋} →
            SigOK n sg → NthG sg s shs → NthSh shs k sh → Γ ⊢ d ∷ El ⌜Nat⌝ →
            Args Γ n sg d sh p → Γ ⊢ conₗ k p ∷ SK sg s d
  ⊢conSyn {n = n} {s = s} {Γ = Γ} {sg = sg} {shs = shs} {sh = sh} {d = d} {p = p} ok ng nh dd as =
    ⊢conₛₜ {Tss = stels sg} {Ts = tels shs} {T = tel sh (var vz)} ⊢⌜Nat⌝ (sigOK ok)
           (nth-stels ng) (nth-tels nh) dd
      (subst (λ X → Γ ⊢ p ∷ El (dpay (SI n) (SD sg) X)) (sym (sub-tel (single (pair (tag s) d)) sh (var vz)))
             (⊢payArgs (⊢SD ok) (nthSh-ok (nthG-ok ok ng) nh) (⊢ix (nthG-lt ng) dd) (step (βsnd _ _) done) as))

  -- …from the payload at its normal form (the telescope instantiated at the index)
  ⊢conV : {Γ : Ctx} {sg : Sig n} {shs : Shapes c} {sh : Shape} {d p : RTm ⌊ Γ ⌋} →
          SigOK n sg → NthG sg s shs → NthSh shs k sh → Γ ⊢ d ∷ El ⌜Nat⌝ →
          Γ ⊢ p ∷ El (dpay (SI n) (SD sg) ⌜ tel sh (pair (tag s) d) ⌝ᵗ) → Γ ⊢ conₗ k p ∷ SK sg s d
  ⊢conV {n = n} {s = s} {Γ = Γ} {sg = sg} {shs = shs} {sh = sh} {d = d} {p = p} ok ng nh dd dp =
    ⊢conₛₜ {Tss = stels sg} {Ts = tels shs} {T = tel sh (var vz)} ⊢⌜Nat⌝ (sigOK ok)
           (nth-stels ng) (nth-tels nh) dd
      (subst (λ X → Γ ⊢ p ∷ El (dpay (SI n) (SD sg) X)) (sym (sub-tel (single (pair (tag s) d)) sh (var vz))) dp)

------------------------------------------------------------------------
-- 5. THE FAMILY IS CLOSED: substitution fixes it.
------------------------------------------------------------------------

private
  tels-sub : (σ : Sub Δ Θ) (shs : Shapes c) → subC (extS σ) ⌜ tels {Δ = Δ} shs ⌝ₛ ≡ ⌜ tels shs ⌝ₛ
  tels-sub σ []ˢʰ         = refl
  tels-sub σ (sh ∷ˢʰ shs) = cong₂ _∷_ (sub-tel (extS σ) sh (var vz)) (tels-sub σ shs)

  sds-sub : (σ : Sub Δ Θ) (sg : Sig n) → subC (extS σ) (SDs ⌜ stels {Δ = Δ} sg ⌝ₛₛ) ≡ SDs ⌜ stels sg ⌝ₛₛ
  sds-sub σ []ᵍ         = refl
  sds-sub σ (shs ∷ᵍ sg) =
    cong₂ _∷_ (trans (Dσ-sub (extS σ) ⌜ tels shs ⌝ₛ) (cong Dσ (tels-sub σ shs)))
              (sds-sub σ sg)

SD-sub : (σ : Sub Δ Θ) (sg : Sig n) → subTm σ (SD {Δ = Δ} sg) ≡ SD sg
SD-sub σ sg =
  cong lam (trans (sel-sub (extS σ) (SDs ⌜ stels sg ⌝ₛₛ) (fst (var vz)))
                  (cong (λ X → sel X (fst (var vz))) (sds-sub σ sg)))

SD-ren : (ρ : Ren Δ Θ) {sg : Sig n} → renTm ρ (SD {Δ = Δ} sg) ≡ SD sg
SD-ren ρ {sg} = trans (sym (subTm-var ρ (SD sg))) (SD-sub ⟨ ρ ⟩ᵣ sg)
  where open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTm-var )

opaque
  unfolding SK
  SK-sub : (σ : Sub Δ Θ) (sg : Sig n) (s : ℕ) (d : RTm Δ) → subTy σ (SK sg s d) ≡ SK sg s (subTm σ d)
  SK-sub {n = n} σ sg s d =
    trans (cong (λ I → IMu I (subTm σ (SD sg)) (subTm σ (pair (tag s) d))) (SI-sub σ n))
          (cong₂ (λ D j → IMu (SI n) D j) (SD-sub σ sg) (cong₂ pair (tag-sub σ s) refl))

-- …and renaming, whose cast is what keeps the checker from normalising
--   the whole description under `renTm` (measured: 20 s per occurrence)
SK-ren : (ρ : Ren Δ Θ) (sg : Sig n) (s : ℕ) (d : RTm Δ) → renTy ρ (SK sg s d) ≡ SK sg s (renTm ρ d)
SK-ren ρ sg s d = trans (sym (subTy-var ρ (SK sg s d))) (trans (SK-sub ⟨ ρ ⟩ᵣ sg s d) (cong (SK sg s) (subTm-var ρ d)))
  where open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )

-- a term of the syntax, one binder further out; the newest variable
⊢wkSK : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {sg : Sig n} {s : ℕ} {d t : RTm ⌊ Γ ⌋} →
        Γ ⊢ t ∷ SK sg s d → (Γ ▹ B) ⊢ renTm vs t ∷ SK sg s (renTm vs d)
⊢wkSK {sg = sg} {s} {d} dt = ⊢-cast (SK-ren vs sg s d) (⊢wk dt)

hereSK : {Γ : Ctx} {sg : Sig n} {s : ℕ} {d : RTm ⌊ Γ ⌋} → (Γ ▹ SK sg s d) ⊢ var vz ∷ SK sg s (renTm vs d)
hereSK {sg = sg} {s} {d} = ⊢-cast (SK-ren vs sg s d) (⊢var here)
