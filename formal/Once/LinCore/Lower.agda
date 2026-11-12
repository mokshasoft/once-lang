-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Lower — plan 0.146 B1.4b, part 2: the image to the flat
-- machine (`AbstractTrace`), D415/D416.
--
-- * Block `j` (the `j`-th key of the program's universe, `allK`) is an
--   `e-fn` entry named by `j`, in a frame of `EP + OP + 2` slots: its two
--   regions (`Layout`) and two save slots. A call passes, in `Input1`, the
--   caller's slot `bot − M` (`bot` the argument's end, `M` the larger of the
--   argument's and the result's words) and, in `Output`, the top view's
--   buffer; the block copies its argument and view in, and at its end its
--   result out (D147).
-- * A call through a cell's code word goes to block `j`'s TRAMPOLINE, an
--   `e-thunk` entry with a frame of its own: it does the cell's part (moves
--   what the cell holds out, frees it — no freed cell is read — or copies it
--   into a fresh cell) and calls block `j` by name.
-- * Every offset is a constant of the code's shape; moves are word by word
--   through `Output`.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.List using (List; []; _∷_; _++_; concat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Target.Symbol using (showNat)
open import Once.CCC.Label using (LabelId; mkLabelId; e-fn; e-thunk)
open import Once.CCC.Machine.SMCore
  using ( AbstractInstr; AbstractTrace; instr-ctrl; c-label; c-jmp; c-branch-tag-zero; c-entry; c-ret
        ; c-call-fn; c-start; c-leave; load-from-slot; store-at-slot; lea-slot; restore-input; mov-to-input
        ; mov-to-output; load-at; store-at; addr-at; instr-alloc-heap; instr-free-heap; instr-load-tag-lit
        ; instr-load-code-addr; instr-save-closure-reg; instr-call-closure; instr-sigop )

module Once.LinCore.Lower
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw

------------------------------------------------------------------------
-- 1. MOVES, word by word through `Output`.
------------------------------------------------------------------------

-- `n` words from slots `a…` to slots `b…`, lowest first (safe when b ≤ a)
mvSS : ℕ → ℕ → ℕ → AbstractTrace
mvSS a b zero    = []
mvSS a b (suc n) = load-from-slot a ∷ store-at-slot b ∷ mvSS (suc a) (suc b) n

-- …highest first (safe when a ≤ b)
mvSSd : ℕ → ℕ → ℕ → AbstractTrace
mvSSd a b zero    = []
mvSSd a b (suc n) = load-from-slot (a + n) ∷ store-at-slot (b + n) ∷ mvSSd a b n

-- from `Input1`'s words `o…` to slots `b…`
mvPS : ℕ → ℕ → ℕ → AbstractTrace
mvPS o b zero    = []
mvPS o b (suc n) = load-at o ∷ store-at-slot b ∷ mvPS (suc o) (suc b) n

-- from slots `a…` to `Input1`'s words `o…`
mvSP : ℕ → ℕ → ℕ → AbstractTrace
mvSP a o zero    = []
mvSP a o (suc n) = load-from-slot a ∷ store-at o ∷ mvSP (suc a) (suc o) n

------------------------------------------------------------------------
-- 2. NAMES: a block by its index, its jump labels, its trampoline.
------------------------------------------------------------------------

nameOf : ℕ → CanonicalName
nameOf j = canonical ("once-lincore" ∷ showNat j ∷ [])

jl : ℕ → ℕ → LabelId
jl j m = mkLabelId (nameOf j) [] (suc m)

tl : ℕ → LabelId
tl j = mkLabelId (nameOf j) [] 0

-- a member's index
idx : ∀ {A : Set} {x : A} {xs} → x ∈ xs → ℕ
idx (here _)  = 0
idx (there p) = suc (idx p)

-- a cell's header: contents-word, code, copy, free
hdr : ℕ
hdr = 4

------------------------------------------------------------------------
-- 3. ★ THE LOWERING of a program's code, inside its universe.
--
-- `ldConst` loads a base constant into `Output` (the target's encoding of a
-- word, a parameter until B1.7 wires the path); `ncty` is the universe's
-- fact that a ν's contents type is among its types (`KeysRun.ncty`).
------------------------------------------------------------------------

module Lowering (U : Univ)
                (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
                (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr) where
  open In U

  -- the frame's save slots, above both regions
  sv₁ sv₂ : Frame → ℕ
  sv₁ φ = budget φ
  sv₂ φ = suc (budget φ)

  fbudget : Frame → ℕ
  fbudget φ = suc (suc (budget φ))

  -- an operand stack's first word
  Tp : Frame → List LTy → ℕ
  Tp φ S = opAt φ S

  -- a cell's code words, from its keys' indices
  header : ℕ → ℕ → ℕ → ℕ → AbstractTrace
  header w jb jc jf =
    instr-alloc-heap (hdr + w) ∷ mov-to-input ∷ addr-at hdr ∷ store-at 0
    ∷ instr-load-code-addr (tl jb) ∷ store-at 1 ∷ instr-load-code-addr (tl jc) ∷ store-at 2
    ∷ instr-load-code-addr (tl jf) ∷ store-at 3 ∷ []

  -- a `prim`: a generator that touches at most one cell
  lowP : ∀ {Γ} (ds : Defs Γ) {A B} (g : LTm Γ A B) → Frame → (S : List LTy) → PrimIn ds g → AbstractTrace
  lowP ds ρl φ S p                = []
  lowP ds ρl⁻ φ S p               = []
  lowP ds lul φ S p               = []
  lowP ds lul⁻ φ S p              = []
  lowP ds lassoc φ S p            = []
  lowP ds lassoc⁻ φ S p           = []
  lowP ds (lclo F q) φ S p        = []
  lowP ds drop φ S p              = []
  lowP ds (lswap {A = A} {B = B}) φ S p =
    let t = Tp φ ((A ⊗t B) ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
    in mvSS t tmp wA ++ mvSS (t + wA) t wB ++ mvSS tmp (t + wB) wA
  lowP ds (linl {A = A} {B = B}) φ S p =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B
    in mvSS (bot ∸ wsz A) (bot ∸ M) (wsz A) ++ instr-load-tag-lit 0 ∷ store-at-slot (bot ∸ suc M) ∷ []
  lowP ds (linr {A = A} {B = B}) φ S p =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B
    in mvSS (bot ∸ wsz B) (bot ∸ M) (wsz B) ++ instr-load-tag-lit 1 ∷ store-at-slot (bot ∸ suc M) ∷ []
  lowP ds (lIn {F = F}) φ S p =
    let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
    in instr-alloc-heap wL ∷ mov-to-input ∷ mvSP (bot ∸ wL) 0 wL ++ mov-to-output ∷ store-at-slot (bot ∸ 1) ∷ []
  lowP ds (lOutμ {F = F}) φ S p =
    let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
    in restore-input (bot ∸ 1) ∷ mvPS 0 (bot ∸ wL) wL ++ instr-free-heap wL ∷ []
  lowP ds (lconst v) φ S p = ldConst v ∷ store-at-slot (Tp φ S ∸ 1) ∷ []
  lowP ds (lop s) φ S p =
    let bot = Tp φ S
    in lea-slot (bot ∸ wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info s)
       ∷ store-at-slot (bot ∸ wsz ⌜ scod s ⌝) ∷ []
  lowP ds (llam {X = X} b γ) φ S (kb , x) =
    let bot = Tp φ S ; wX = wsz X
    in header wX (idx kb) (idx (inC x)) (idx (inF x)) ++ mvSP (bot ∸ wX) hdr wX
       ++ mov-to-output ∷ store-at-slot (bot ∸ 1) ∷ []
  lowP ds (llamω {X = X} b γ) φ S (kb , x) =
    let bot = Tp φ S ; wX = wsz X
    in header wX (idx kb) (idx (inC x)) (idx (inF x)) ++ mvSP (bot ∸ wX) hdr wX
       ++ mov-to-output ∷ store-at-slot (bot ∸ 1) ∷ []
  lowP ds (lunf {F = F} {S = S₀}) φ S (n , o) =
    let bot = Tp φ S ; wP = wsz (cty (F , S₀))
    in header wP (idx (inO o n)) (idx (inC (ncty n))) (idx (inF (ncty n))) ++ mvSP (bot ∸ wP) hdr wP
       ++ mov-to-output ∷ store-at-slot (bot ∸ 1) ∷ []
  {-# CATCHALL #-}
  lowP ds g φ S p = []

  -- ★ an instruction and a code, at their shapes, in block `j`'s frame;
  -- `m` the next jump label; `fin` what the code's `end` becomes
  lowI : ∀ {sh sh′} → Frame → ℕ → ℕ → (i : Insᴵ sh sh′) → IIn i → AbstractTrace × ℕ
  lowC : ∀ {sh T′} → Frame → ℕ → ℕ → AbstractTrace → (c : Codeᴵ sh T′) → CIn c → AbstractTrace × ℕ

  lowI φ j m unpair ev  = [] , m
  lowI φ j m pair ev    = [] , m
  lowI φ j m unit ev    = [] , m
  lowI φ j m untag ev   = [] , m
  lowI φ j m untag₁ ev  = [] , m
  lowI φ j m tag₁ ev    = [] , m
  lowI φ j m elift ev   = [] , m
  lowI φ j m epop ev    = [] , m
  lowI φ j m stuck ev   = [] , m
  lowI φ j m (swap {A = A} {B} {S}) ev =
    let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
    in mvSS t tmp wA ++ mvSS (t + wA) t wB ++ mvSS tmp (t + wB) wA , m
  lowI φ j m (prim ds {S = S} g) ev = lowP ds g φ S ev , m
  lowI φ j m (elend {E} {Es} {X} {A} {S}) ev =
    let e = ws Es ; wE = wsz E
    in mvSS e (e + wE) wE ++ mvSS (Tp φ ((X ⊗t A) ∷ S)) (e + wE + wE) (wsz X) , m
  lowI φ j m (eunlend {E} {Es} {X} {B} {S}) ev =
    let e = ws Es ; wE = wsz E
    in mvSS (e + wE + wE) (Tp φ (B ∷ S) ∸ wsz X) (wsz X) , m
  lowI φ j m (efst {E₁} {E₂} {Es}) ev =
    let e = ws Es in mvSS e (e + wsz (E₁ ⊗t E₂)) (wsz E₁) , m
  lowI φ j m (esnd {E₁} {E₂} {Es}) ev =
    let e = ws Es in mvSS (e + wsz E₁) (e + wsz (E₁ ⊗t E₂)) (wsz E₂) , m
  lowI φ j m (eout {F} {Es}) ev =
    let e = ws Es in restore-input e ∷ mvPS 0 (suc e) (wsz (LF∙ F (μt F))) , m
  lowI φ j m (eoutq {F} {Es}) ev =
    let e = ws Es in restore-input e ∷ mvPS 0 (suc e) (wsz (LF∙ F (μt F))) , m
  lowI φ j m (eapp {l} {X} {Es}) ev =
    let e = ws Es in mvSS e (e + wsz X) (wsz X) , m
  lowI φ j m (eword {b} {Es} {S}) ev = mvSS (ws Es) (Tp φ S ∸ 1) 1 , m
  -- ★ a call by name: the argument's area in `Input1`, the top view's buffer in `Output`
  lowI φ j m (call {bsig nothing A B} {Es} {S} κ) κ∈ =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B
    in lea-slot (bot ∸ M) ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf (idx κ∈))) ∷ [] , m
  lowI φ j m (call {bsig (just E) A B} {Es} {S} κ) κ∈ =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B
    in lea-slot (bot ∸ M) ∷ mov-to-input ∷ lea-slot (ws Es) ∷ instr-ctrl (c-call-fn (nameOf (idx κ∈))) ∷ [] , m
  -- ★ through a cell's code word: the cell in `fclosure`, the caller's area in `Output`
  lowI φ j m (icall {Es} {g} {A} {B} {S}) ev =
    let bot = Tp φ S ; t = Tp φ ((Fn once g A B ⊗t A) ∷ S)
    in restore-input t ∷ lea-slot (bot ∸ (suc (wsz A) ⊔ wsz B)) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [] , m
  lowI φ j m (icallω {Es} {g} {A} {B} {S}) ev =
    let bot = Tp φ S
    in restore-input (ws Es) ∷ lea-slot (bot ∸ (wsz A ⊔ wsz B)) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [] , m
  lowI φ j m (iobs ds {Es} {F} {S}) ev =
    let bot = Tp φ S
    in restore-input (bot ∸ 1) ∷ lea-slot (bot ∸ (1 ⊔ wsz (LF∙ F (Nu F)))) ∷ instr-save-closure-reg ∷ instr-call-closure ∷ [] , m
  -- a copy through word 2: `fclosure` the cell + 1, `Input1` the destination, `Output` the cell
  lowI φ j m (ccopy {Es} {S = S}) ev =
    restore-input (ws Es) ∷ addr-at 1 ∷ mov-to-input ∷ instr-save-closure-reg
    ∷ lea-slot (Tp φ S ∸ 1) ∷ mov-to-input ∷ load-from-slot (ws Es) ∷ instr-call-closure ∷ [] , m
  lowI φ j m (ncopy {Es} {S = S}) ev =
    restore-input (ws Es) ∷ addr-at 1 ∷ mov-to-input ∷ instr-save-closure-reg
    ∷ lea-slot (Tp φ S ∸ 1) ∷ mov-to-input ∷ load-from-slot (ws Es) ∷ instr-call-closure ∷ [] , m
  -- a free through word 3: `fclosure` the cell + 2, `Output` the cell
  lowI φ j m (cfree {Es} {S = S}) ev =
    let c = Tp φ S ∸ 1
    in restore-input c ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
       ∷ restore-input c ∷ mov-to-output ∷ instr-call-closure ∷ [] , m
  lowI φ j m (nfree {Es} {S = S}) ev =
    let c = Tp φ S ∸ 1
    in restore-input c ∷ addr-at 2 ∷ mov-to-input ∷ instr-save-closure-reg
       ∷ restore-input c ∷ mov-to-output ∷ instr-call-closure ∷ [] , m
  -- ★ the loop: the round, its end the dispatch; `inr` turns, `inl` falls through
  lowI φ j m (loop {E} {Es} {A} {B} {S} c) ev =
    let Lh = jl j m ; Ld = jl j (suc m) ; Li = jl j (suc (suc m))
        body = lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) c ev
        t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
    in instr-ctrl (c-label Lh) ∷ proj₁ body
       ++ instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li)
       ∷ mvSSd (suc t) (bot ∸ wsz A) (wsz A) ++ instr-ctrl (c-jmp Lh)
       ∷ instr-ctrl (c-label Li) ∷ mvSSd (suc t) (bot ∸ wsz B) (wsz B)
       , proj₂ body

  lowC φ j m fin end ev = fin , m
  lowC φ j m fin halted ev = [] , m
  lowC φ j m fin (i ⨾ c) (ei , ec) =
    let li = lowI φ j m i ei ; lc = lowC φ j (proj₂ li) fin c ec
    in proj₁ li ++ proj₁ lc , proj₂ lc
  lowC φ j m fin (case {Es} {A} {B} {S} c₁ c₂) (e₁ , e₂) =
    let L₁ = jl j m ; t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S
        l₂ = lowC φ j (suc m) fin c₂ e₂ ; l₁ = lowC φ j (proj₂ l₂) fin c₁ e₁
    in lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero L₁)
       ∷ mvSSd (suc t) (bot ∸ wsz B) (wsz B) ++ proj₁ l₂
       ++ instr-ctrl (c-label L₁) ∷ mvSSd (suc t) (bot ∸ wsz A) (wsz A) ++ proj₁ l₁
       , proj₂ l₁
  lowC φ j m fin (ecase {E₁} {E₂} {Es} c₁ c₂) (e₁ , e₂) =
    let L₁ = jl j m ; e = ws Es ; nb = e + wsz (E₁ ⊕t E₂)
        l₂ = lowC φ j (suc m) fin c₂ e₂ ; l₁ = lowC φ j (proj₂ l₂) fin c₁ e₁
    in lea-slot e ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero L₁)
       ∷ mvSS (suc e) nb (wsz E₂) ++ proj₁ l₂
       ++ instr-ctrl (c-label L₁) ∷ mvSS (suc e) nb (wsz E₁) ++ proj₁ l₁
       , proj₂ l₁

  ----------------------------------------------------------------------
  -- 4. BLOCKS AND TRAMPOLINES.
  ----------------------------------------------------------------------

  -- ★ block `j`: save the argument's area and the view's buffer, copy them
  -- in, run, copy the result out, return
  lowBlock : ∀ {σ} (j : ℕ) (κ : Key σ) → CIn (blockᴵ κ) → AbstractTrace
  lowBlock {bsig t A B} j κ ev =
    let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B ; b = fbudget φ
        view = view-in t
        fin = restore-input (sv₁ φ) ∷ mvSP (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret b) ∷ []
    in instr-ctrl (c-entry (e-fn (nameOf j)) b)
       ∷ store-at-slot (sv₂ φ) ∷ mov-to-output ∷ store-at-slot (sv₁ φ)
       ∷ mvPS (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A) ++ view φ
       ++ proj₁ (lowC φ j 0 fin (blockᴵ κ) ev)
    where
      view-in : Maybe LTy → Frame → AbstractTrace
      view-in nothing  φ = []
      view-in (just E) φ = restore-input (sv₂ φ) ∷ mvPS 0 0 (wsz E)

  -- ★ block `j`'s trampoline, by its key: the cell's part, then the block
  tramp : ∀ {σ} (j : ℕ) → Key σ → AbstractTrace
  -- one-shot body: the environment out of the cell, the argument from the
  -- caller, the cell freed, the block, the result back
  tramp j (kbody1 {X = X} {A = A} {B = B} ds b γ) =
    let wX = wsz X ; wA = wsz A ; wB = wsz B ; M = (wX + wA) ⊔ wB ; Mc = suc wA ⊔ wB ; a = M ∸ (wX + wA)
    in instr-ctrl (c-entry (e-thunk (tl j)) (suc (suc M)))
       ∷ store-at-slot (suc M) ∷ mov-to-output ∷ store-at-slot M
       ∷ mvPS hdr a wX ++ restore-input (suc M) ∷ mvPS (Mc ∸ wA) (a + wX) wA
       ++ restore-input M ∷ instr-free-heap (hdr + wX)
       ∷ lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf j))
       ∷ restore-input (suc M) ∷ mvSP (M ∸ wB) (Mc ∸ wB) wB ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
  -- many-use body: the caller's area as is, the view the cell's contents
  tramp j (kbodyω ds b γ) =
    instr-ctrl (c-entry (e-thunk (tl j)) 1)
    ∷ store-at-slot 0 ∷ addr-at hdr ∷ restore-input 0 ∷ instr-ctrl (c-call-fn (nameOf j))
    ∷ instr-ctrl (c-ret 1) ∷ []
  -- observation: the coalgebra and seed out of the cell, the cell freed
  tramp j (kobs ds F S) =
    let wP = wsz (cty (F , S)) ; wL = wsz (LF∙ F (Nu F)) ; M = wP ⊔ wL ; Mc = 1 ⊔ wL
    in instr-ctrl (c-entry (e-thunk (tl j)) (suc (suc M)))
       ∷ store-at-slot (suc M) ∷ mov-to-output ∷ store-at-slot M
       ∷ mvPS hdr (M ∸ wP) wP ++ restore-input M ∷ instr-free-heap (hdr + wP)
       ∷ lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf j))
       ∷ restore-input (suc M) ∷ mvSP (M ∸ wL) (Mc ∸ wL) wL ++ instr-ctrl (c-ret (suc (suc M))) ∷ []
  -- a copy of a cell: its contents copied (the view the cell's), then a
  -- fresh cell with the same code words
  tramp j (kcopy T₀) =
    let w = wsz T₀ ; s₁ = w ; s₂ = suc w ; s₃ = suc (suc w) ; b = suc s₃
    in instr-ctrl (c-entry (e-thunk (tl j)) b)
       ∷ store-at-slot s₂ ∷ mov-to-output ∷ store-at-slot s₁
       ∷ restore-input s₂ ∷ addr-at hdr ∷ store-at-slot s₃
       ∷ lea-slot 0 ∷ mov-to-input ∷ load-from-slot s₃ ∷ instr-ctrl (c-call-fn (nameOf j))
       ∷ instr-alloc-heap (hdr + w) ∷ store-at-slot s₃
       ∷ restore-input s₂ ∷ load-at 1 ∷ restore-input s₃ ∷ store-at 1
       ∷ restore-input s₂ ∷ load-at 2 ∷ restore-input s₃ ∷ store-at 2
       ∷ restore-input s₂ ∷ load-at 3 ∷ restore-input s₃ ∷ store-at 3
       ∷ addr-at hdr ∷ store-at 0 ∷ mvSP 0 hdr w
       ++ restore-input s₁ ∷ load-from-slot s₃ ∷ store-at 0 ∷ instr-ctrl (c-ret b) ∷ []
  -- a free of a cell: its contents out, the cell freed, then their free
  tramp j (kfree T₀) =
    let w = wsz T₀
    in instr-ctrl (c-entry (e-thunk (tl j)) (suc w))
       ∷ store-at-slot w ∷ restore-input w ∷ mvPS hdr 0 w ++ instr-free-heap (hdr + w)
       ∷ lea-slot 0 ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf j)) ∷ instr-ctrl (c-ret (suc w)) ∷ []
  -- a fold is never called through a cell
  tramp j (kfold ds F alg) = []

  ----------------------------------------------------------------------
  -- 5. ★ THE IMAGE: the start, then every key's block and trampoline.
  ----------------------------------------------------------------------

  -- the keys with their indices and their blocks' evidence
  blocksOf : ∀ (ks : List AKey) → (∀ {κ} → κ ∈ ks → BIn κ) → ℕ → AbstractTrace
  blocksOf []             ev j = []
  blocksOf ((σ , κ) ∷ ks) ev j = lowBlock j κ (ev (here refl)) ++ tramp j κ ++ blocksOf ks (λ p → ev (there p)) (suc j)
    where open import Relation.Binary.PropositionalEquality using (refl)

module Program′ {Γ} (ds : Defs Γ) (f : LTm Γ One One) (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr) where
  open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
  open Program ds f using (U; blocks-in; start-in)
  open ProgramRun ds f using (ncty)
  open Lowering U ncty ldConst public

  -- ★ the program's image: its start (the main term, ending in the Host's
  -- `leave`), then its blocks
  image : AbstractTrace
  image =
    let main = compᴵ ds f {[]} {[]} end ; φ = frameOf main ; b = fbudget φ
    in instr-ctrl (c-start b) ∷ proj₁ (lowC φ 0 0 (instr-ctrl c-leave ∷ []) main (start-in {[]} {[]} tt))
       ++ blocksOf (allK U) blocks-in 0
