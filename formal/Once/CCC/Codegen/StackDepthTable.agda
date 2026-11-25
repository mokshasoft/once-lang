-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.StackDepthTable — D488: COMPUTING the depth table.
--
-- Nothing here is proved: the table it returns is a candidate, and the pass
-- uses it only if `StackDepth.consistent?` accepts it (else the fallback `T₀`).
-- So the maps need no invariant, only speed: a height-balanced tree (unverified)
-- over keys encoded as lists of numbers, compared lexicographically.
--
-- WHICH CALLS ARE CHECKED (D488). A checked call costs its function nothing, so
-- only a cycle of UNCHECKED calls has no static depth. One depth-first pass over
-- the call graph, memoized, computes each function's depth once, its callees
-- first: a call that meets a function still in progress closes a cycle, and that
-- function is made unbounded (every call to it checked); so is one deeper than
-- `d-max` (no check then asks for much more). The indirect calls are checked
-- when some closure body makes one, directly or through what it calls; else the
-- closure bodies go first and give the bound `clo-dep`.
------------------------------------------------------------------------

module Once.CCC.Codegen.StackDepthTable where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Char using (Char)
import Data.Char
open import Data.List using (List; []; _∷_; _++_; length; map; concatMap; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _<ᵇ_; _≡ᵇ_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)
import Data.String
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Label using (EntryId; e-fn; e-thunk; LabelId; mkLabelId; _≡ᵇᴱ_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.CCC.Codegen.StackDepth
  using (Owner; o-start; o-entry; own; Kind; kind; k-call; k-clo; k-sig; k-entry; k-label; k-jump; k-none
        ; Depths; depths; cost; _≡ᵇᴼ_)

------------------------------------------------------------------------
-- KEYS
------------------------------------------------------------------------
Key : Set
Key = List ℕ

enc-name : CanonicalName → Key
enc-name (canonical ps) = concatMap enc-part ps
  where
    enc-part : Data.String.String → Key
    enc-part s = length cs ∷ map Data.Char.toℕ cs
      where cs = Data.String.toList s

enc-label : LabelId → Key
enc-label (mkLabelId n p i) = enc-name n ++ (length p ∷ p) ++ (i ∷ [])

enc-entry : EntryId → Key
enc-entry (e-fn n)    = 0 ∷ enc-name n
enc-entry (e-thunk ℓ) = 1 ∷ enc-label ℓ

data Cmp : Set where
  lt eq gt : Cmp

cmp : Key → Key → Cmp
cmp []      []      = eq
cmp []      (_ ∷ _) = lt
cmp (_ ∷ _) []      = gt
cmp (x ∷ a) (y ∷ b) = if x <ᵇ y then lt else (if y <ᵇ x then gt else cmp a b)

------------------------------------------------------------------------
-- A HEIGHT-BALANCED TREE (unverified)
------------------------------------------------------------------------
data Map (V : Set) : Set where
  tip : Map V
  bin : ℕ → Map V → Key → V → Map V → Map V

module _ {V : Set} where
  height : Map V → ℕ
  height tip             = 0
  height (bin h _ _ _ _) = h

  node : Map V → Key → V → Map V → Map V
  node l k v r = bin (suc (height l ⊔ height r)) l k v r

  rotR : Map V → Key → V → Map V → Map V
  rotR (bin _ ll lk lv lr) k v r = node ll lk lv (node lr k v r)
  rotR tip                 k v r = node tip k v r

  rotL : Map V → Key → V → Map V → Map V
  rotL l k v (bin _ rl rk rv rr) = node (node l k v rl) rk rv rr
  rotL l k v tip                 = node l k v tip

  -- left heavy by two: a single or a double rotation
  fixL : Map V → Key → V → Map V → Map V
  fixL l@(bin _ ll lk lv lr) k v r =
    if height ll <ᵇ height lr then rotR (rotL ll lk lv lr) k v r else rotR l k v r
  fixL tip k v r = node tip k v r

  fixR : Map V → Key → V → Map V → Map V
  fixR l k v r@(bin _ rl rk rv rr) =
    if height rr <ᵇ height rl then rotL l k v (rotR rl rk rv rr) else rotL l k v r
  fixR l k v tip = node l k v tip

  balance : Map V → Key → V → Map V → Map V
  balance l k v r =
    if suc (height r) <ᵇ height l then fixL l k v r
    else (if suc (height l) <ᵇ height r then fixR l k v r else node l k v r)

  insert : Key → V → Map V → Map V
  insert k v tip               = node tip k v tip
  insert k v (bin h l k′ v′ r) = go (cmp k k′)
    where
      go : Cmp → Map V
      go lt = balance (insert k v l) k′ v′ r
      go gt = balance l k′ v′ (insert k v r)
      go eq = bin h l k v r

  lookup : Map V → Key → Maybe V
  lookup tip               k = nothing
  lookup (bin _ l k′ v r) k = go (cmp k k′)
    where
      go : Cmp → Maybe V
      go lt = lookup l k
      go gt = lookup r k
      go eq = just v

  fromList : List (Key × V) → Map V
  fromList = foldr (λ kv m → insert (Data.Product.proj₁ kv) (Data.Product.proj₂ kv) m) tip
    where import Data.Product

------------------------------------------------------------------------
-- ONE FUNCTION'S ROW: bounded?, depth past its frame, its frame
------------------------------------------------------------------------
record Row : Set where
  constructor row
  field
    r-bnd   : Bool
    r-past  : ℕ
    r-frame : ℕ

maybe : ∀ {A B : Set} → B → (A → B) → Maybe A → B
maybe d f nothing  = d
maybe d f (just x) = f x

-- the table a map of rows (and the start's depth, the closure bound, the labels) stands for
toDepths : Map Row → ℕ → Bool → ℕ → Map Owner → Depths
toDepths m p₀ clo-c clo-d lm = depths
  (λ e → maybe true Row.r-bnd (lookup m (enc-entry e)))
  (λ e → maybe 0 (λ r → Row.r-frame r + Row.r-past r) (lookup m (enc-entry e)))
  (λ e → maybe 0 Row.r-past (lookup m (enc-entry e)))
  p₀ clo-c clo-d false
  (λ ℓ → maybe o-start (λ o → o) (lookup lm (enc-label ℓ)))

------------------------------------------------------------------------
-- THE IMAGE, AS THE TABLE READS IT: its functions, each its frame and what
-- its instructions do to the depth (one scan; keys encoded once)
------------------------------------------------------------------------
data Op : Set where
  op-call : Key → EntryId → Op     -- a direct call
  op-clo  : Op                     -- an indirect call
  op-sig  : ℕ → Op                 -- a SigOp's words

record Seg : Set where
  constructor seg
  field
    sg-own   : Owner
    sg-frame : ℕ
    sg-ops   : List Op

op-of : Kind → Maybe Op
op-of (k-call g) = just (op-call (enc-entry g) g)
op-of k-clo      = just op-clo
op-of (k-sig w)  = just (op-sig w)
{-# CATCHALL #-}
op-of _          = nothing

segments : AbstractTrace → List Seg
segments t = go t o-start 0 [] []
  where
    go : AbstractTrace → Owner → ℕ → List Op → List Seg → List Seg
    go []      o f ops done = seg o f ops ∷ done
    go (i ∷ r) o f ops done = at (kind i)
      where
        o′ = own o i
        more : Maybe Op → List Op
        more (just x) = x ∷ ops
        more nothing  = ops
        at : Kind → List Seg
        at (k-entry e fr) = go r o′ fr [] (seg o f ops ∷ done)
        {-# CATCHALL #-}
        at k = if o′ ≡ᵇᴼ o then go r o f (more (op-of k)) done
               else go r o′ 0 (single (op-of k)) (seg o f ops ∷ done)
          where
            single : Maybe Op → List Op
            single (just x) = x ∷ []
            single nothing  = []

-- the entries' segments, by key
seg-map : List Seg → Map Seg
seg-map []                          = tip
seg-map (seg o-start f ops ∷ ss)    = seg-map ss
seg-map (sg@(seg (o-entry e) f ops) ∷ ss) = insert (enc-entry e) sg (seg-map ss)

------------------------------------------------------------------------
-- PHASE 1: does a function make an indirect call, itself or through a callee?
-- (memoized; a function in progress counts as not — a cycle may under-count,
-- and then the certificate fails and the fallback is taken)
------------------------------------------------------------------------
data RSt : Set where
  r-busy : RSt
  r-fin  : Bool → RSt

reach : ℕ → Map Seg → Key → Map RSt → Bool × Map RSt
reach-ops : ℕ → Map Seg → List Op → Map RSt → Bool × Map RSt
reach-seg : ℕ → Map Seg → Key → Maybe Seg → Map RSt → Bool × Map RSt
reach zero    sm k m = false , m
reach (suc n) sm k m = by (lookup m k)
  where
    by : Maybe RSt → Bool × Map RSt
    by (just r-busy)    = false , m
    by (just (r-fin b)) = b , m
    by nothing          = reach-seg n sm k (lookup sm k) (insert k r-busy m)
reach-seg n sm k nothing  m = false , insert k (r-fin false) m
reach-seg n sm k (just (seg _ _ ops)) m = fin (reach-ops n sm ops m)
  where fin : Bool × Map RSt → Bool × Map RSt
        fin (b , m′) = b , insert k (r-fin b) m′
reach-ops n sm []                  m = false , m
reach-ops n sm (op-clo ∷ ops)      m = true , m
reach-ops n sm (op-sig _ ∷ ops)    m = reach-ops n sm ops m
reach-ops n sm (op-call k _ ∷ ops) m = more (reach n sm k m)
  where more : Bool × Map RSt → Bool × Map RSt
        more (true , m′)  = true , m′
        more (false , m′) = reach-ops n sm ops m′

-- some closure body reaches an indirect call: then indirect calls are checked
clo-cycle : ℕ → List Seg → Map Seg → Bool
clo-cycle fuel ss sm = go ss tip
  where
    go : List Seg → Map RSt → Bool
    go []                                  m = false
    go (seg (o-entry (e-thunk ℓ)) _ _ ∷ ss) m = any (reach fuel sm (enc-entry (e-thunk ℓ)) m)
      where any : Bool × Map RSt → Bool
            any (true , _)   = true
            any (false , m′) = go ss m′
    {-# CATCHALL #-}
    go (_ ∷ ss)                            m = go ss m

------------------------------------------------------------------------
-- PHASE 2: every function's depth, callees first
------------------------------------------------------------------------
-- THE DEPTH CAP: a function deeper than this (its frame and past, in words) is
-- not bounded — calls to it are checked — so no check asks for more than about
-- this, and the start's depth stays within its reserve (a heuristic: any value
-- is sound, the certificate decides)
d-max : ℕ
d-max = 4096

data DSt : Set where
  d-busy : Bool → DSt                -- in progress (and met again: on a cycle)
  d-fin  : Row → DSt

-- the depth of a call to the function at `k`: `just` its whole depth when it may go unchecked
depth : ℕ → Bool → ℕ → Map Seg → Key → Map DSt → Maybe ℕ × Map DSt
depth-seg : ℕ → Bool → ℕ → Map Seg → Key → EntryId → Seg → Map DSt → Maybe ℕ × Map DSt
depth-ops : ℕ → Bool → ℕ → Map Seg → EntryId → List Op → Map DSt → ℕ × Map DSt
depth zero    cc cd sm k m = nothing , m
depth (suc n) cc cd sm k m = by (lookup m k)
  where
    by : Maybe DSt → Maybe ℕ × Map DSt
    by (just (d-busy _))           = nothing , insert k (d-busy true) m
    by (just (d-fin (row b p f)))  = (if b then just (f + p) else nothing) , m
    by nothing                     = from (lookup sm k)
      where from : Maybe Seg → Maybe ℕ × Map DSt
            from nothing                      = just 0 , m      -- not in the image: as the table's default
            from (just sg@(seg (o-entry e) _ _)) = depth-seg n cc cd sm k e sg (insert k (d-busy false) m)
            from (just (seg o-start _ _))     = just 0 , m
depth-seg n cc cd sm k e (seg _ f ops) m = fin (depth-ops n cc cd sm e ops m)
  where
    fin : ℕ × Map DSt → Maybe ℕ × Map DSt
    fin (p , m′) = done (lookup m′ k)
      where
        cut : Maybe DSt → Bool
        cut (just (d-busy c)) = c
        {-# CATCHALL #-}
        cut _                 = false
        done : Maybe DSt → Maybe ℕ × Map DSt
        done st = let b = not (cut st) ∧ (f + p ≤ᵇ d-max)
                  in (if b then just (f + p) else nothing) , insert k (d-fin (row b p f)) m′
depth-ops n cc cd sm e []        m = 0 , m
depth-ops n cc cd sm e (x ∷ ops) m = one x
  where
    rest : ℕ → Map DSt → ℕ × Map DSt
    rest c m′ = add c (depth-ops n cc cd sm e ops m′)
      where add : ℕ → ℕ × Map DSt → ℕ × Map DSt
            add c (p , m″) = c ⊔ p , m″
    one : Op → ℕ × Map DSt
    one (op-sig w)    = rest w m
    one op-clo        = rest (if cc then 0 else suc cd) m
    one (op-call k g) = if g ≡ᵇᴱ e then rest 0 m else call (depth n cc cd sm k m)
      where call : Maybe ℕ × Map DSt → ℕ × Map DSt
            call (just d , m′)  = rest (suc d) m′
            call (nothing , m′) = rest 0 m′

-- the start's segments, at the end (their calls, the functions')
start-ops : ℕ → Bool → ℕ → Map Seg → List Seg → Map DSt → ℕ × Map DSt
start-ops n cc cd sm []                       m = 0 , m
start-ops n cc cd sm (seg o-start _ ops ∷ ss) m = both (depth-ops n cc cd sm (e-fn (canonical [])) ops m)
  where both : ℕ × Map DSt → ℕ × Map DSt
        both (p , m′) = more (start-ops n cc cd sm ss m′)
          where more : ℕ × Map DSt → ℕ × Map DSt
                more (q , m″) = p ⊔ q , m″
{-# CATCHALL #-}
start-ops n cc cd sm (_ ∷ ss)                 m = start-ops n cc cd sm ss m

-- every entry (the closure bodies first, when they bound the indirect calls)
all-entries : ℕ → Bool → ℕ → Map Seg → Bool → List Seg → Map DSt → Map DSt
all-entries n cc cd sm only-thunks []       m = m
all-entries n cc cd sm only-thunks (sg ∷ ss) m = one (Seg.sg-own sg)
  where
    visit : EntryId → Map DSt
    visit e = all-entries n cc cd sm only-thunks ss (Data.Product.proj₂ (depth (suc n) cc cd sm (enc-entry e) m))
      where import Data.Product
    one : Owner → Map DSt
    one (o-entry (e-thunk ℓ)) = visit (e-thunk ℓ)
    one (o-entry (e-fn g))    = if only-thunks then all-entries n cc cd sm only-thunks ss m else visit (e-fn g)
    one o-start               = all-entries n cc cd sm only-thunks ss m

-- the closure bodies' bound, and the rows
clo-max : List Seg → Map DSt → ℕ
clo-max []                                  m = 0
clo-max (seg (o-entry (e-thunk ℓ)) _ _ ∷ ss) m = at (lookup m (enc-entry (e-thunk ℓ))) ⊔ clo-max ss m
  where at : Maybe DSt → ℕ
        at (just (d-fin (row _ p f))) = f + p
        {-# CATCHALL #-}
        at _                          = 0
{-# CATCHALL #-}
clo-max (_ ∷ ss)                            m = clo-max ss m

rows-of : List Seg → Map DSt → Map Row
rows-of []                          m = tip
rows-of (seg (o-entry e) _ _ ∷ ss)  m = at (lookup m (enc-entry e))
  where at : Maybe DSt → Map Row
        at (just (d-fin r)) = insert (enc-entry e) r (rows-of ss m)
        {-# CATCHALL #-}
        at _                = rows-of ss m
rows-of (seg o-start _ _ ∷ ss)      m = rows-of ss m

-- the labels' owners (one scan)
labels : AbstractTrace → Map Owner
labels t = go o-start t tip
  where
    go : Owner → AbstractTrace → Map Owner → Map Owner
    go o []      m = m
    go o (i ∷ r) m = go (own o i) r (add (kind i))
      where
        add : Kind → Map Owner
        add (k-label ℓ) = insert (enc-label ℓ) (own o i) m
        {-# CATCHALL #-}
        add _           = m

-- THE CANDIDATE
table : AbstractTrace → Depths
table t = build (clo-cycle fuel ss sm)
  where
    ss   = segments t
    sm   = seg-map ss
    fuel = suc (length ss)
    build : Bool → Depths
    build cc = finish (all-entries fuel cc cd sm false ss m₁)
      where
        -- the closure bodies first (when indirect calls go unchecked, they bound them)
        m₁ = if cc then tip else all-entries fuel cc 0 sm true ss tip
        cd = if cc then 0 else clo-max ss m₁
        finish : Map DSt → Depths
        finish m = from (start-ops fuel cc cd sm ss m)
          where from : ℕ × Map DSt → Depths
                from (p₀ , m′) = toDepths (rows-of ss m′) p₀ cc (clo-max ss m′) (labels t)
