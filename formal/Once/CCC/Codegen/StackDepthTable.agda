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
-- ROUNDS. From a table, one scan of the image gives every function's depth past
-- its frame under it (each instruction's `cost`) and whether its calls are all
-- to its own function or to bounded callees (then calls to IT may go unchecked).
-- From nothing bounded, round `k` bounds the functions whose calls nest `k`
-- deep; a function on a cycle never is. The rounds stop when one changes
-- nothing, or after one per entry.
------------------------------------------------------------------------

module Once.CCC.Codegen.StackDepthTable where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Char using (Char)
import Data.Char
open import Data.List using (List; []; _∷_; _++_; length; map; concatMap; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
import Data.String
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Label using (EntryId; e-fn; e-thunk; LabelId; mkLabelId)
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

-- the table a map of rows (and the start's row, the closure bound, the labels) stands for
toDepths : Map Row → ℕ → Bool → ℕ → Map Owner → Depths
toDepths m p₀ clo-b clo-d lm = depths
  (λ e → maybe false Row.r-bnd (lookup m (enc-entry e)))
  (λ e → maybe 0 (λ r → Row.r-frame r + Row.r-past r) (lookup m (enc-entry e)))
  (λ e → maybe 0 Row.r-past (lookup m (enc-entry e)))
  p₀ (not clo-b) clo-d false
  (λ ℓ → maybe o-start (λ o → o) (lookup lm (enc-label ℓ)))

------------------------------------------------------------------------
-- ONE ROUND: a scan under `T`, a row per function
------------------------------------------------------------------------
-- a call at owner `o` that may go unchecked under `T` keeps `o` bounded
call-ok : Depths → Owner → Kind → Bool
call-ok T o (k-call g) = (o ≡ᵇᴼ o-entry g) ∨ Depths.bnd T g
call-ok T o k-clo      = not (Depths.clo-chk T)
{-# CATCHALL #-}
call-ok T o _          = true

-- the scan's state: the function so far (its owner, row), and the rows done
record Scan : Set where
  constructor scan
  field
    s-own  : Owner
    s-row  : Row
    s-done : List (Owner × Row)

flush : Scan → List (Owner × Row)
flush (scan o r d) = (o , r) ∷ d

step : Depths → Scan → AbstractInstr → Scan
step T (scan o (row b p f) d) i = go (kind i)
  where
    o′ = own o i
    c  = cost T o′ i
    go : Kind → Scan
    go (k-entry e fr) = scan o′ (row true c fr) ((o , row b p f) ∷ d)
    {-# CATCHALL #-}
    go k              = scan o (row (b ∧ call-ok T o′ k) (p ⊔ c) f) d

rows : Depths → AbstractTrace → List (Owner × Row)
rows T t = flush (go t (scan o-start (row true 0 0) []))
  where
    go : AbstractTrace → Scan → Scan
    go []      s = s
    go (i ∷ r) s = go r (step T s i)

-- the start's, the entries', the closure bodies'
record Summary : Set where
  constructor summary
  field
    m-rows  : Map Row
    m-p₀    : ℕ
    m-clo-b : Bool
    m-clo-d : ℕ

summarize : List (Owner × Row) → Summary
summarize []                         = summary tip 0 true 0
summarize ((o-start , r) ∷ rs)       = add (summarize rs)
  where add : Summary → Summary
        add (summary m p b d) = summary m (Row.r-past r ⊔ p) b d
summarize ((o-entry e , r) ∷ rs)     = add e (summarize rs)
  where
    dep = Row.r-frame r + Row.r-past r
    add : EntryId → Summary → Summary
    add (e-thunk ℓ) (summary m p b d) = summary (insert (enc-entry (e-thunk ℓ)) r m) p (b ∧ Row.r-bnd r) (dep ⊔ d)
    add (e-fn n)    (summary m p b d) = summary (insert (enc-entry (e-fn n)) r m) p b d

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

------------------------------------------------------------------------
-- THE ROUNDS
------------------------------------------------------------------------
same-rows : List (Owner × Row) → List (Owner × Row) → Bool
same-rows []                   []                   = true
same-rows ((o , row b p f) ∷ a) ((o′ , row b′ p′ f′) ∷ a′) =
  (o ≡ᵇᴼ o′) ∧ (b ≡ᵇᴮ b′) ∧ (p ≡ᵇ p′) ∧ (f ≡ᵇ f′) ∧ same-rows a a′
  where
    _≡ᵇᴮ_ : Bool → Bool → Bool
    true  ≡ᵇᴮ y = y
    false ≡ᵇᴮ y = not y
{-# CATCHALL #-}
same-rows _ _ = false

entries : AbstractTrace → ℕ
entries []      = 0
entries (i ∷ t) = go (kind i) + entries t
  where
    go : Kind → ℕ
    go (k-entry _ _) = 1
    {-# CATCHALL #-}
    go _             = 0

-- the candidate table: rounds from nothing bounded until nothing changes
table : AbstractTrace → Depths
table t = iter (suc (suc (entries t))) T-init (rows T-init t)
  where
    lm = labels t
    of : List (Owner × Row) → Depths
    of rs = go (summarize rs)
      where go : Summary → Depths
            go (summary m p b d) = toDepths m p b d lm
    T-init : Depths
    T-init = depths (λ _ → false) (λ _ → 0) (λ _ → 0) 0 true 0 false (λ _ → o-start)
    iter : ℕ → Depths → List (Owner × Row) → Depths
    iter zero    T rs = of rs
    iter (suc n) T rs = next (of rs)
      where
        next : Depths → Depths
        next T′ = stop (rows T′ t)
          where
            stop : List (Owner × Row) → Depths
            stop rs′ = if same-rows rs rs′ then T′ else iter n T′ rs′
