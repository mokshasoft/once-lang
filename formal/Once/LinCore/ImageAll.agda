-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageAll — plan 0.146 B1.6: ★ EVERY INSTRUCTION OF THE NEW
-- IMAGE IS ONE THE ARCH LAYER COVERS, EVERY ALLOCATION HAS A WORD, EVERY
-- NAME IT USES IS A KEY'S.
--
-- The image is `c-start b ∷ tail`. One traversal of the tail proves of every
-- instruction `EmittableI` (no frame op, no retired fixed-offset form, no
-- room check, no start), `AllocMinI` (a cell of one word at least) and `Ref`
-- (a call names a key's block, a code word a key's trampoline, which starts
-- with its entry). All three reduce to `⊤` on every concrete instruction but
-- an allocation, a call by name and a code word, so the proofs are the
-- lowering's shape: an allocation's word is `1 ⊔ w` (a μ node, `Lower.lIn`)
-- or `hdr + w` (a cell with a header); a name is a key's index, by its
-- membership in the universe. From it, seven of `Emitted`'s fields:
-- `em-image`, `em-alloc`, the start's `em-budget`/`em-zero`/`em-start` (no
-- start in the tail), and `em-calls`/`em-code` (by `EntriesI`'s landing). The
-- traversal is `Labels`'/`LabelsC`'s, over the same clauses.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m⊔n; +-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (e-thunk)
open import Once.Type using (FitsInReg)
open import Once.Semantics.Machine using (LitPayload)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Name using (CanonicalName)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Codegen.RoomChecksFacts using (All-room)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.FrameFree using (EmittableI; ImageI; emittable-image)
import Once.CCC.Machine.AllocMin

module Once.LinCore.ImageAll
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; Lit)
open import Once.IR.Semantics.Trace using (T; call)
open Sig using (info)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Image fmt bw
open import Once.LinCore.Keys fmt bw
open Univ using (tys; nus; ops)
open import Once.LinCore.Layout fmt bw
open import Once.LinCore.Values fmt bw using (wsz; hdr)
open import Once.LinCore.Lower fmt bw
open import Once.LinCore.MoveCode using (mvPS; mvSP; mvSS; mvSSd; stores)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)

-- a constant's loader is an `instr-load-const` (what the arch layer covers,
-- no allocation, no name)
LoadConst : ∀ (ldConst : ∀ {b} → Lit b → AbstractInstr) → Set
LoadConst ldConst = ∀ {b} (v : Lit b) → Σ _ λ A → Σ (FitsInReg A) λ p → Σ (LitPayload p) λ x → ldConst v ≡ instr-load-const p x

-- `nm`: the definition `AllocMin` is applied to (its `AllocMinI` does not
-- depend on it, but two applications are two stuck terms; `Emitted`'s is
-- the arch layer's, at the program's name)
module Ok (nm : CanonicalName) (U : Univ)
          (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
          (ldConst : ∀ {b} → Lit b → AbstractInstr) where
  open In U
  open Lowering U ncty ldConst

  -- a key's trampoline starts with its entry
  TrEntry : ∀ {σ} → ℕ → Key σ → Set
  TrEntry j κ = Σ ℕ λ b → Σ AbstractTrace λ r → tramp j κ ≡ instr-ctrl (c-entry (e-thunk (tl j)) b) ∷ r

  -- a name the image uses is a key's
  Ref : AbstractInstr → Set
  Ref (instr-ctrl (c-call-fn f))  = Σ AKey λ a → Σ (a ∈ allK U) λ p → f ≡ nameOf (idx p)
  Ref (instr-load-code-addr ℓ)    = Σ AKey λ a → Σ (a ∈ allK U) λ p → ℓ ≡ tl (idx p) × TrEntry (idx p) (proj₂ a)
  -- (D462) an op's call is what an op of the universe lowers to (itself, or a
  -- comparison's block: `opSig`), so its block is the image's (`ImageOwned`)
  Ref (instr-sigop si)            = Σ Sig λ s → s ∈ ops U × sig si ≡ opSig s (cmpOf s)
  -- D468: the image holds no allocator record word (the expansion adds them)
  Ref (load-rec _)                = ⊥
  Ref (store-rec _)               = ⊥
  {-# CATCHALL #-}
  Ref _                           = ⊤

  OK : AbstractInstr → Set
  OK i = EmittableI i × Once.CCC.Machine.AllocMin.AllocMinI i × Ref i

  -- an instruction the three predicates reduce to `⊤` on
  pattern ✓ = tt , tt , tt

  ----------------------------------------------------------------------
  -- 1. MOVES, CELLS, NAMES.
  ----------------------------------------------------------------------

  mvSS-ok : ∀ a b n → All OK (mvSS a b n)
  mvSS-ok a b zero    = []
  mvSS-ok a b (suc n) = ✓ ∷ ✓ ∷ mvSS-ok (suc a) (suc b) n

  mvSSd-ok : ∀ a b n → All OK (mvSSd a b n)
  mvSSd-ok a b zero    = []
  mvSSd-ok a b (suc n) = ✓ ∷ ✓ ∷ mvSSd-ok a b n

  mvPS-ok : ∀ o b n → All OK (mvPS o b n)
  mvPS-ok o b zero    = []
  mvPS-ok o b (suc n) = ✓ ∷ ✓ ∷ mvPS-ok (suc o) (suc b) n

  mvSP-ok : ∀ a o n → All OK (mvSP a o n)
  mvSP-ok a o zero    = []
  mvSP-ok a o (suc n) = ✓ ∷ ✓ ∷ mvSP-ok (suc a) (suc o) n

  stores-ok : ∀ b n → All OK (stores b n)
  stores-ok b zero    = []
  stores-ok b (suc n) = ✓ ∷ stores-ok (suc b) n

  -- a cell with a header has `hdr` words at least
  cell-word : ∀ w → OK (instr-alloc-heap (hdr + w))
  cell-word w = tt , s≤s z≤n , tt

  contentsAddr-ok : ∀ w → OK (contentsAddr w)
  contentsAddr-ok zero    = ✓
  contentsAddr-ok (suc w) = ✓

  -- a call by a key's name; the same, at the index the key is at
  callRef : ∀ {a} (p : a ∈ allK U) → OK (instr-ctrl (c-call-fn (nameOf (idx p))))
  callRef p = tt , tt , (_ , p , refl)

  callAt : ∀ {a j} (p : a ∈ allK U) → idx p ≡ j → OK (instr-ctrl (c-call-fn (nameOf j)))
  callAt p refl = callRef p

  -- a code word: a key's trampoline
  codeRef : ∀ {a} (p : a ∈ allK U) → TrEntry (idx p) (proj₂ a) → OK (instr-load-code-addr (tl (idx p)))
  codeRef p te = tt , tt , (_ , p , refl , te)

  ----------------------------------------------------------------------
  -- 2. ★ THE LOWERING.
  ----------------------------------------------------------------------

  module Low (ld-is : LoadConst ldConst) where

    ld-ok : ∀ {b} (v : Lit b) → OK (ldConst v)
    ld-ok v = ld-go (ld-is v)
      where ld-go : (Σ _ λ A → Σ (FitsInReg A) λ p → Σ (LitPayload p) λ x → ldConst v ≡ instr-load-const p x) → OK (ldConst v)
            ld-go (_ , p , x , e) = subst OK (sym e) ✓

    header-ok : ∀ w jb jc jf → OK (instr-load-code-addr (tl jb)) → OK (instr-load-code-addr (tl jc))
              → OK (instr-load-code-addr (tl jf)) → All OK (header w jb jc jf)
    header-ok w jb jc jf ob oc of = cell-word w ∷ ✓ ∷ ✓ ∷ ✓ ∷ ob ∷ ✓ ∷ oc ∷ ✓ ∷ of ∷ ✓ ∷ []

    argIn-ok : ∀ {A} (b : ST.Base ST.∅ₖ A) bot w → OK (argIn b bot w)
    argIn-ok (ST.b-var {i = ()} _) bot w
    argIn-ok ST.b-Unit    bot w = ✓
    argIn-ok ST.b-Void    bot w = ✓
    argIn-ok ST.b-Int     bot w = ✓
    argIn-ok ST.b-Float   bot w = ✓
    argIn-ok (ST.b-* _ _) bot w = ✓
    argIn-ok (ST.b-+ _ _) bot w = ✓

    answer-ok : ∀ {B} (b : ST.Base ST.∅ₖ B) bot → All OK (answer b bot)
    answer-ok (ST.b-var {i = ()} _) bot
    answer-ok ST.b-Unit    bot = []
    answer-ok ST.b-Void    bot = []
    answer-ok ST.b-Int     bot = ✓ ∷ []
    answer-ok ST.b-Float   bot = ✓ ∷ []
    answer-ok (ST.b-* _ _) bot = []
    answer-ok (ST.b-+ _ _) bot = []

    ansDst-ok : ∀ {B} (b : ST.Base ST.∅ₖ B) bot w → All OK (ansDst b bot w)
    ansDst-ok (ST.b-var {i = ()} _) bot w
    ansDst-ok ST.b-Unit    bot w = []
    ansDst-ok ST.b-Void    bot w = []
    ansDst-ok ST.b-Int     bot w = []
    ansDst-ok ST.b-Float   bot w = []
    ansDst-ok (ST.b-* _ _) bot w = ✓ ∷ []
    ansDst-ok (ST.b-+ _ _) bot w = ✓ ∷ []

    lowOp-ok : ∀ s (p : s ∈ ops U) c (e : cmpOf s ≡ c) bot → All OK (lowOp s c bot)
    lowOp-ok s p nothing e bot =
      argIn-ok (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ ✓
      ∷ ++⁺ (ansDst-ok (SigOpInfo.conB (info s)) bot (wsz ⌜ scod s ⌝))
            ((tt , tt , s , p , sym (cong (opSig s) e)) ∷ answer-ok (SigOpInfo.conB (info s)) bot)
    lowOp-ok s p (just c) e bot =
      argIn-ok (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ ✓ ∷ (tt , tt , s , p , sym (cong (opSig s) e)) ∷ ✓ ∷ ✓ ∷ []

    -- a cell's build: its header (its code words the keys' trampolines), its contents, its address
    cell-ok : ∀ w {ab ac af} (pb : ab ∈ allK U) (pc : ac ∈ allK U) (pf : af ∈ allK U)
            → TrEntry (idx pb) (proj₂ ab) → TrEntry (idx pc) (proj₂ ac) → TrEntry (idx pf) (proj₂ af)
            → ∀ a o d → All OK (header w (idx pb) (idx pc) (idx pf) ++ mvSP a o w ++ mov-to-output ∷ store-at-slot d ∷ [])
    cell-ok w pb pc pf tb tc tf a o d =
      ++⁺ (header-ok w (idx pb) (idx pc) (idx pf) (codeRef pb tb) (codeRef pc tc) (codeRef pf tf)) (++⁺ (mvSP-ok a o w) (✓ ∷ ✓ ∷ []))

    lowP-ok : ∀ {Γ} (ds : Defs Γ) {A B} (g : LTm Γ A B) φ S (p : PrimIn ds g) → All OK (lowP ds g φ S p)
    lowP-ok ds lid φ S p          = []
    lowP-ok ds (_ ∘l _) φ S p     = []
    lowP-ok ds (_ ⊗l _) φ S p     = []
    lowP-ok ds ρl φ S p           = []
    lowP-ok ds ρl⁻ φ S p          = []
    lowP-ok ds lul φ S p          = []
    lowP-ok ds lul⁻ φ S p         = []
    lowP-ok ds lassoc φ S p       = []
    lowP-ok ds lassoc⁻ φ S p      = []
    lowP-ok ds (lswap {A = A} {B = B}) φ S p =
      let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
      in ++⁺ (mvSS-ok t tmp wA) (++⁺ (mvSS-ok (t + wA) t wB) (mvSS-ok tmp (t + wB) wA))
    lowP-ok ds dup φ S p          = []
    lowP-ok ds drop φ S p         = []
    lowP-ok ds (linl {A = A} {B = B}) φ S p =
      let bot = Tp φ S ; M = wsz A ⊔ wsz B
      in ++⁺ (mvSS-ok (bot ∸ wsz A) (bot ∸ M) (wsz A)) (✓ ∷ ✓ ∷ stores-ok (bot ∸ (M ∸ wsz A)) (M ∸ wsz A))
    lowP-ok ds (linr {A = A} {B = B}) φ S p =
      let bot = Tp φ S ; M = wsz A ⊔ wsz B
      in ++⁺ (mvSS-ok (bot ∸ wsz B) (bot ∸ M) (wsz B)) (✓ ∷ ✓ ∷ stores-ok (bot ∸ (M ∸ wsz B)) (M ∸ wsz B))
    lowP-ok ds (lcase _ _) φ S p  = []
    lowP-ok ds lzero φ S p        = []
    -- ★ a μ node's cell: `1 ⊔` its layer's words
    lowP-ok ds (lIn {F = F}) φ S p =
      let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
      in (tt , m≤m⊔n 1 wL , tt) ∷ ✓ ∷ ++⁺ (mvSP-ok (bot ∸ wL) 0 wL) (✓ ∷ ✓ ∷ [])
    lowP-ok ds (lOutμ {F = F}) φ S p =
      let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
      in ✓ ∷ ++⁺ (mvPS-ok 0 (bot ∸ wL) wL) (✓ ∷ [])
    lowP-ok ds (lcata _ _) φ S p  = []
    lowP-ok ds (lclo _ _) φ S p   = []
    lowP-ok ds (lapp _) φ S p     = []
    lowP-ok ds (lend _) φ S p     = []
    lowP-ok ds (blift _) φ S p    = []
    lowP-ok ds bcopy φ S p        = []
    lowP-ok ds (llam {X = X} b γ) φ S (kb , x) =
      cell-ok (wsz X) kb (inC x) (inF x) (_ , _ , refl) (_ , _ , refl) (_ , _ , refl) (Tp φ S ∸ wsz X) hdr (Tp φ S ∸ 1)
    lowP-ok ds (llamω {X = X} b γ) φ S (kb , x) =
      cell-ok (wsz X) kb (inC x) (inF x) (_ , _ , refl) (_ , _ , refl) (_ , _ , refl) (Tp φ S ∸ wsz X) hdr (Tp φ S ∸ 1)
    lowP-ok ds lev φ S p          = []
    lowP-ok ds (lunf {F = F} {S = S₀}) φ S (n , o) =
      cell-ok (wsz (cty (F , S₀))) (inO o n) (inC (ncty n)) (inF (ncty n)) (_ , _ , refl) (_ , _ , refl) (_ , _ , refl)
              (Tp φ S ∸ wsz (cty (F , S₀))) hdr (Tp φ S ∸ 1)
    lowP-ok ds lout φ S p         = []
    lowP-ok ds (lconst v) φ S p   = ld-ok v ∷ ✓ ∷ []
    lowP-ok ds (lop s) φ S p      = lowOp-ok s p (cmpOf s) refl (Tp φ S)
    lowP-ok ds (liter _ _) φ S p  = []

    mutual
      lowI-ok : ∀ φ j m {sh sh′} (i : Insᴵ sh sh′) (ei : IIn i) → All OK (proj₁ (lowI φ j m i ei))
      lowI-ok φ j m unpair ei  = []
      lowI-ok φ j m pair ei    = []
      lowI-ok φ j m unit ei    = []
      lowI-ok φ j m untag ei   = []
      lowI-ok φ j m untag₁ ei  = []
      lowI-ok φ j m tag₁ ei    = []
      lowI-ok φ j m elift ei   = []
      lowI-ok φ j m epop ei    = []
      lowI-ok φ j m stuck ei   = []
      lowI-ok φ j m (swap {A = A} {B} {S}) ei =
        let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
        in ++⁺ (mvSS-ok t tmp wA) (++⁺ (mvSS-ok (t + wA) t wB) (mvSS-ok tmp (t + wB) wA))
      lowI-ok φ j m (prim ds {S = S} g) ei = lowP-ok ds g φ S ei
      lowI-ok φ j m (elend {E} {Es} {X} {A} {S}) ei =
        let e = ws Es ; wE = wsz E
        in ++⁺ (mvSS-ok e (e + wE) wE) (mvSS-ok (Tp φ ((X ⊗t A) ∷ S)) (e + wE + wE) (wsz X))
      lowI-ok φ j m (eunlend {E} {Es} {X} {B} {S}) ei =
        let e = ws Es ; wE = wsz E in mvSS-ok (e + wE + wE) (Tp φ (B ∷ S) ∸ wsz X) (wsz X)
      lowI-ok φ j m (efst {E₁} {E₂} {Es}) ei = mvSS-ok (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁)
      lowI-ok φ j m (esnd {E₁} {E₂} {Es}) ei = mvSS-ok (ws Es + wsz E₁) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₂)
      lowI-ok φ j m (eout {F} {Es}) ei  = ✓ ∷ mvPS-ok 0 (suc (ws Es)) (wsz (LF∙ F (μt F)))
      lowI-ok φ j m (eoutq {F} {Es}) ei = ✓ ∷ mvPS-ok 0 (suc (ws Es)) (wsz (LF∙ F (μt F)))
      lowI-ok φ j m (eapp {l} {X} {Es}) ei = mvSS-ok (ws Es) (ws Es + wsz X) (wsz X)
      lowI-ok φ j m (eword {b} {Es} {S}) ei = mvSS-ok (ws Es) (Tp φ S ∸ 1) 1
      -- a call by name: a key's block
      lowI-ok φ j m (call {bsig nothing A B} κ) ei  = ✓ ∷ ✓ ∷ callRef ei ∷ []
      lowI-ok φ j m (call {bsig (just E) A B} κ) ei = ✓ ∷ ✓ ∷ ✓ ∷ callRef ei ∷ []
      lowI-ok φ j m icall ei   = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m icallω ei  = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m (iobs ds) ei = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m ccopy ei   = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m ncopy ei   = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m cfree ei   = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m nfree ei   = ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ []
      lowI-ok φ j m open1 ei   = []
      lowI-ok φ j m openω ei   = []
      lowI-ok φ j m nopen ei   = []
      lowI-ok φ j m copen ei   = []
      lowI-ok φ j m reclose ei = []
      lowI-ok φ j m fopen ei   = []
      -- the loop: its head, the body, the dispatch, the exit
      lowI-ok φ j m (loop {E} {Es} {A} {B} {S} c) ev =
        let t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
        in ✓ ∷ ++⁺ (lowC-ok φ j (suc (suc (suc m))) _ (✓ ∷ []) c ev)
                   (✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvSSd-ok (suc t) (bot ∸ wsz A) (wsz A)) (✓ ∷ ✓ ∷ mvSSd-ok (suc t) (bot ∸ wsz B) (wsz B)))

      lowC-ok : ∀ φ j m fin → All OK fin → ∀ {sh T} (c : Codeᴵ sh T) (ev : CIn c) → All OK (proj₁ (lowC φ j m fin c ev))
      lowC-ok φ j m fin fok end ev    = fok
      lowC-ok φ j m fin fok halted ev = ✓ ∷ []
      lowC-ok φ j m fin fok (i ⨾ c) (ei , ec) =
        ++⁺ (lowI-ok φ j m i ei) (lowC-ok φ j (proj₂ (lowI φ j m i ei)) fin fok c ec)
      lowC-ok φ j m fin fok (case {Es} {A} {B} {S} c₁ c₂) (e₁ , e₂) =
        let t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S ; l₂ = lowC φ j (suc m) fin c₂ e₂
        in ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvSSd-ok (suc t) (bot ∸ wsz B) (wsz B))
             (++⁺ (lowC-ok φ j (suc m) fin fok c₂ e₂)
               (✓ ∷ ++⁺ (mvSSd-ok (suc t) (bot ∸ wsz A) (wsz A)) (lowC-ok φ j (proj₂ l₂) fin fok c₁ e₁)))
      lowC-ok φ j m fin fok (ecase {E₁} {E₂} {Es} c₁ c₂) (e₁ , e₂) =
        let e = ws Es ; nb = e + wsz (E₁ ⊕t E₂) ; l₂ = lowC φ j (suc m) fin c₂ e₂
        in ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvSS-ok (suc e) nb (wsz E₂))
             (++⁺ (lowC-ok φ j (suc m) fin fok c₂ e₂)
               (✓ ∷ ++⁺ (mvSS-ok (suc e) nb (wsz E₁)) (lowC-ok φ j (proj₂ l₂) fin fok c₁ e₁)))

    ----------------------------------------------------------------------
    -- 3. BLOCKS AND TRAMPOLINES.
    ----------------------------------------------------------------------

    view-ok : ∀ t φ → All OK (view-in t φ)
    view-ok nothing  φ = []
    view-ok (just E) φ = ✓ ∷ mvPS-ok 0 0 (wsz E)

    lowBlock-ok : ∀ {σ} j (κ : Key σ) (ev : CIn (blockᴵ κ)) → All OK (lowBlock j κ ev)
    lowBlock-ok {bsig t A B} j κ ev =
      let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B
      in ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvPS-ok (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A))
           (++⁺ (view-ok t φ)
             (lowC-ok φ j 0 _ (✓ ∷ ++⁺ (mvSP-ok (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B)) (✓ ∷ [])) (blockᴵ κ) ev))

    -- block `j`'s trampoline: its call is of block `j`, the key at index `j`
    tramp-ok : ∀ {σ} j (κ : Key σ) (p : (σ , κ) ∈ allK U) → idx p ≡ j → All OK (tramp j κ)
    tramp-ok j (kbody1 {X = X} {A = A} {B = B} ds b γ) p e =
      let wX = wsz X ; wA = wsz A ; wB = wsz B ; M = (wX + wA) ⊔ wB ; Mc = suc wA ⊔ wB ; a = M ∸ (wX + wA)
      in ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvPS-ok hdr a wX)
           (✓ ∷ ++⁺ (mvPS-ok (Mc ∸ wA) (a + wX) wA)
             (✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ callAt p e ∷ ✓ ∷ ++⁺ (mvSP-ok (M ∸ wB) (Mc ∸ wB) wB) (✓ ∷ [])))
    tramp-ok j (kbodyω {X = X} ds b γ) p e = ✓ ∷ ✓ ∷ contentsAddr-ok (wsz X) ∷ ✓ ∷ callAt p e ∷ ✓ ∷ []
    tramp-ok j (kobs ds F S) p e =
      let wP = wsz (cty (F , S)) ; wL = wsz (LF∙ F (Nu F)) ; M = wP ⊔ wL ; Mc = 1 ⊔ wL
      in ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvPS-ok hdr (M ∸ wP) wP)
           (✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ callAt p e ∷ ✓ ∷ ++⁺ (mvSP-ok (M ∸ wL) (Mc ∸ wL) wL) (✓ ∷ []))
    tramp-ok j (kcopy T₀) p e =
      let w = wsz T₀
      in ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ contentsAddr-ok w ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ callAt p e ∷ cell-word w
         ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ ✓
         ∷ ++⁺ (mvSP-ok 0 hdr w) (✓ ∷ ✓ ∷ ✓ ∷ ✓ ∷ [])
    tramp-ok j (kfree T₀) p e =
      let w = wsz T₀
      in ✓ ∷ ✓ ∷ ✓ ∷ ++⁺ (mvPS-ok hdr 0 w) (✓ ∷ ✓ ∷ ✓ ∷ callAt p e ∷ ✓ ∷ [])
    tramp-ok j (kfold ds F alg) p e = []
    tramp-ok j (ktr1 ds b γ) p e = []
    tramp-ok j (ktrω ds b γ) p e = []
    tramp-ok j (ktro ds F S) p e = []
    tramp-ok j (ktrc X C) p e    = []
    tramp-ok j (ktrf X C) p e    = []

    -- the blocks from `j`: `ks` is the universe's keys from index `j`
    blocks-ok : ∀ (ks : List AKey) (ev : ∀ {κ} → κ ∈ ks → BIn κ) j
              → (∀ {a} (q : a ∈ ks) → Σ (a ∈ allK U) λ p → idx p ≡ j + idx q)
              → All OK (blocksOf ks ev j)
    blocks-ok []             ev j at = []
    blocks-ok ((σ , κ) ∷ ks) ev j at =
      ++⁺ (lowBlock-ok j κ (ev (here refl)))
          (++⁺ (tramp-ok j κ (proj₁ (at (here refl))) (trans (proj₂ (at (here refl))) (+-identityʳ j)))
               (blocks-ok ks (λ q → ev (there q)) (suc j) at′))
      where
        at′ : ∀ {a} (q : a ∈ ks) → Σ (a ∈ allK U) λ p → idx p ≡ suc j + idx q
        at′ q = proj₁ (at (there q)) , trans (proj₂ (at (there q))) (+-suc j (idx q))

----------------------------------------------------------------------
-- 4. ★ THE IMAGE.
----------------------------------------------------------------------

module Img (nm : CanonicalName) {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr) (ld-is : LoadConst ldConst) where
  open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
  open Program ds f using (U; blocks-in; start-in)
  open Program ds f using (ncty)
  open Program′ ds f ldConst
  open Lowering U ncty ldConst
  open Ok nm U ncty ldConst
  open Low ld-is

  main = compᴵ ds f {[]} {[]} end
  φ₀ = frameOf main

  -- the image past its start
  tail : AbstractTrace
  tail = proj₁ (lowC φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) main (start-in {[]} {[]} tt)) ++ blocksOf (allK U) blocks-in 0

  tail-ok : All OK tail
  tail-ok = ++⁺ (lowC-ok φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) (✓ ∷ []) main (start-in {[]} {[]} tt))
                (blocks-ok (allK U) blocks-in 0 (λ q → q , refl))

  -- ★ `Emitted`'s pointwise fields: every instruction the arch layer
  -- covers, the start as the start (`em-image`); a word in every cell (`em-alloc`)
  em-image : All ImageI image
  em-image = tt ∷ Data.List.Relation.Unary.All.map (λ {i} p → emittable-image i (proj₁ p)) tail-ok

  em-alloc : All (Once.CCC.Machine.AllocMin.AllocMinI) image
  em-alloc = tt ∷ Data.List.Relation.Unary.All.map (λ p → proj₁ (proj₂ p)) tail-ok

  -- ★ (D462) every op call of the image, room-checked, is what an op of the
  -- universe lowers to (`Ref`'s `instr-sigop` case): its block is the image's
  SigIn : AbstractInstr → Set
  SigIn i = ∀ {A B} (si : SigOpInfo A B) → i ≡ instr-sigop si → Σ Sig λ s → s ∈ ops U × sig si ≡ opSig s (cmpOf s)

  private
    sig-in : ∀ i → OK i → SigIn i
    sig-in .(instr-sigop si) o si refl = proj₂ (proj₂ o)

  sigops : ∀ {A B} (si : SigOpInfo A B) → instr-sigop si ∈ room-checks image → Σ Sig λ s → s ∈ ops U × sig si ≡ opSig s (cmpOf s)
  sigops {A} {B} si m = Data.List.Relation.Unary.All.lookup {P = SigIn}
                  (All-room {P = SigIn} image (λ k {A} {B} si ()) ((λ {A} {B} si ()) ∷ Data.List.Relation.Unary.All.map (λ {i} o {A} {B} → sig-in i o {A} {B}) tail-ok)) m {A} {B} si refl

  -- ★ the start: at pc 0, at the main term's budget, and nowhere else
  -- (`EmittableI` refutes it in the tail)
  em-budget : ℕ
  em-budget = fbudget φ₀

  -- the constant loader defines no label (`EntriesI`'s premise)
  ld-nl : ∀ {FS : FrameSemantics} {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing
  ld-nl {FS} v = nl-go (ld-is v)
    where nl-go : (Σ _ λ A → Σ (FitsInReg A) λ p → Σ (LitPayload p) λ x → ldConst v ≡ instr-load-const p x)
                → NoLabels.mark {FS} (ldConst v) ≡ nothing
          nl-go (_ , p , x , e) = subst (λ i → NoLabels.mark {FS} i ≡ nothing) (sym e) refl

  module Fetch {FS : FrameSemantics} where
    open FlatMachine {FS} using (fetch; fetch-All; find-fn; find-thunk)
    open ImgE {FS} ds f ldConst (ld-nl {FS}) using (image-fn; image-tramp)

    em-zero : fetch image 0 ≡ just (instr-ctrl (c-start em-budget))
    em-zero = refl

    em-start : ∀ k b → fetch image k ≡ just (instr-ctrl (c-start b)) → k ≡ 0
    em-start zero    b e = refl
    em-start (suc k) b e = ⊥-elim (proj₁ (fetch-All {P = OK} {prog = tail} {k = k} tail-ok e))

    -- D468: the image holds no allocator record word (the expansion adds them)
    no-lrec : ∀ k w → fetch image k ≡ just (load-rec w) → ⊥
    no-lrec zero    w ()
    no-lrec (suc k) w e = proj₂ (proj₂ (fetch-All {P = OK} {prog = tail} {k = k} tail-ok e))

    no-srec : ∀ k w → fetch image k ≡ just (store-rec w) → ⊥
    no-srec zero    w ()
    no-srec (suc k) w e = proj₂ (proj₂ (fetch-All {P = OK} {prog = tail} {k = k} tail-ok e))

    -- ★ a call names a block of the universe, and lands on it
    em-calls : ∀ k g → fetch image k ≡ just (instr-ctrl (c-call-fn g)) → Σ ℕ (λ j → find-fn image g ≡ just j)
    em-calls zero    g ()
    em-calls (suc k) g e = call-go (proj₂ (proj₂ (fetch-All {P = OK} {prog = tail} {k = k} tail-ok e)))
      where call-go : Ref (instr-ctrl (c-call-fn g)) → Σ ℕ (λ j → find-fn image g ≡ just j)
            call-go (_ , p , e′) = subst (λ z → Σ ℕ (λ j → find-fn image z ≡ just j)) (sym e′) (_ , image-fn p)

    -- ★ a code word names a trampoline, and lands on it
    em-code : ∀ k (ℓ : Once.CCC.Label.LabelId) → fetch image k ≡ just (instr-load-code-addr ℓ)
            → Σ ℕ (λ j → find-thunk image ℓ ≡ just j)
    em-code zero    ℓ ()
    em-code (suc k) ℓ e = code-go (proj₂ (proj₂ (fetch-All {P = OK} {prog = tail} {k = k} tail-ok e)))
      where code-go : Ref (instr-load-code-addr ℓ) → Σ ℕ (λ j → find-thunk image ℓ ≡ just j)
            code-go (_ , p , e′ , (_ , _ , te)) = subst (λ z → Σ ℕ (λ j → find-thunk image z ≡ just j)) (sym e′) (_ , image-tramp p te)
