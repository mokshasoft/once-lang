-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Keys — plan 0.146 B1.4b, part 1: a program reaches FINITELY
-- MANY blocks.
--
-- The image (`Once.LinCore.Image`) calls blocks by `Key`; its code is
-- finite only if a program reaches finitely many keys. They are collected
-- from the program's terms and its table (`Got`), by structure, so the
-- collection is a LIST by construction; what is proved is that it is CLOSED:
--
--   * every key the collection names has a block whose code calls, builds
--     and observes only what the collection names (`blocks-in`);
--   * the copy and free blocks of a type reach its parts (`subs`, closed
--     under `comps`), so a fold's or a deep copy's self-call stays inside;
--   * a closure or a ν is built by a `prim` its code names, so what a CELL
--     will be called, copied, freed or observed with is named too: closure
--     bodies, environment types, ν seeds (`(F , S)`) and the observers' tables.
--
-- The lowering (B1.4b, next) numbers the keys of `allK` into labels.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map; deduplicateᵇ)
import Data.Bool
open import Data.Bool using (Bool; true; false)
import Data.List.Membership.Setoid.Properties
open import Relation.Nullary.Decidable.Core using (T?)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-deduplicate⁻)
open import Data.List.Relation.Unary.Any using (here; there; toSum)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate)
open import Data.List.Relation.Unary.All.Properties using (++⁺; map⁺; ++⁻ˡ; ++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; setoid; cong; cong₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Keys
  (fmt : TargetNum)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base)
open import Once.IR.Semantics.Trace using (T; call)
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.TyEq fmt using (eqT; eqT-ok; eqT-refl)
open import Once.LinCore.Lent fmt using (Fact; elemT; holds; lentTys; lent-closed; shallowO)
open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- 0. Lists.
------------------------------------------------------------------------

cmap : ∀ {A B : Set} → (A → List B) → List A → List B
cmap f []       = []
cmap f (x ∷ xs) = f x ++ cmap f xs

∈-cmap⁺ : ∀ {A B : Set} {f : A → List B} {x y} xs → x ∈ xs → y ∈ f x → y ∈ cmap f xs
∈-cmap⁺ (x ∷ xs) (here refl) m = ∈-++⁺ˡ m
∈-cmap⁺ {f = f} (x ∷ xs) (there p) m = ∈-++⁺ʳ (f x) (∈-cmap⁺ xs p m)

∈-cmap⁻ : ∀ {A B : Set} {f : A → List B} {y} xs → y ∈ cmap f xs → ∃ λ x → x ∈ xs × y ∈ f x
∈-cmap⁻ {f = f} (x ∷ xs) m =
  [ (λ p → x , here refl , p)
  , (λ p → let (z , q , r) = ∈-cmap⁻ xs p in z , there q , r)
  ]′ (∈-++⁻ (f x) m)

one : ∀ {A : Set} {x : A} {ys} → x ∈ ys → (x ∷ []) ⊆ ys
one m (here refl) = m

------------------------------------------------------------------------
-- 1. THE TYPES A COPY OR A FREE REACHES: a type's parts, a μ's layer.
------------------------------------------------------------------------

-- what `copyᴵ`/`freeᴵ` of a type call the copy/free of
comps : LTy → List LTy
comps (A ⊗t B) = A ∷ B ∷ []
comps (A ⊕t B) = A ∷ B ∷ []
comps (Ct l X) = X ∷ []
comps (μt F)   = LF∙ F (μt F) ∷ []
{-# CATCHALL #-}
comps _        = []

-- every type a copy or a free of `T` reaches; a μ's layers by its functor,
-- its own recursive positions cut (they are the μ again)
subs  : LTy → List LTy
inner : LTy → List LTy
subsF  : LF → LF → List LTy
innerF : LF → LF → List LTy

subs T = T ∷ inner T

inner (A ⊗t B) = subs A ++ subs B
inner (A ⊕t B) = subs A ++ subs B
inner (Ct l X) = subs X
inner (μt F)   = subsF F F
{-# CATCHALL #-}
inner _        = []

subsF G F = LF∙ G (μt F) ∷ innerF G F

innerF (Kμ H)   F = subsF H H
innerF (G ⊕f H) F = subsF G F ++ subsF H F
innerF (G ⊗f H) F = subsF G F ++ subsF H F
{-# CATCHALL #-}
innerF _        F = []

-- ★ a μ's layers reach only its layers and itself
closedF : ∀ G F {R : List LTy} → subsF G F ⊆ R → subs (μt F) ⊆ R
        → ∀ {T C} → T ∈ subsF G F → C ∈ comps T → C ∈ R
closedF Idf      F h₁ h₂ (here refl) (here refl) = h₂ (there (here refl))
closedF Idf      F h₁ h₂ (here refl) (there ())
closedF Kone     F h₁ h₂ (here refl) ()
closedF Kzero    F h₁ h₂ (here refl) ()
closedF (Kb b)   F h₁ h₂ (here refl) ()
closedF (Kμ H)   F h₁ h₂ (here refl) (here refl) = h₁ (there (here refl))
closedF (Kμ H)   F h₁ h₂ (here refl) (there ())
closedF (G ⊕f H) F h₁ h₂ (here refl) (here refl) = h₁ (there (here refl))
closedF (G ⊕f H) F h₁ h₂ (here refl) (there (here refl)) = h₁ (there (∈-++⁺ʳ (subsF G F) (here refl)))
closedF (G ⊕f H) F h₁ h₂ (here refl) (there (there ()))
closedF (G ⊗f H) F h₁ h₂ (here refl) (here refl) = h₁ (there (here refl))
closedF (G ⊗f H) F h₁ h₂ (here refl) (there (here refl)) = h₁ (there (∈-++⁺ʳ (subsF G F) (here refl)))
closedF (G ⊗f H) F h₁ h₂ (here refl) (there (there ()))
closedF Idf      F h₁ h₂ (there ())
closedF Kone     F h₁ h₂ (there ())
closedF Kzero    F h₁ h₂ (there ())
closedF (Kb b)   F h₁ h₂ (there ())
closedF (Kμ H)   F h₁ h₂ (there m) c = closedF H H (λ p → h₁ (there p)) h₁ m c
closedF (G ⊕f H) F h₁ h₂ (there m) c =
  [ (λ p → closedF G F (λ q → h₁ (there (∈-++⁺ˡ q))) h₂ p c)
  , (λ p → closedF H F (λ q → h₁ (there (∈-++⁺ʳ (subsF G F) q))) h₂ p c)
  ]′ (∈-++⁻ (subsF G F) m)
closedF (G ⊗f H) F h₁ h₂ (there m) c =
  [ (λ p → closedF G F (λ q → h₁ (there (∈-++⁺ˡ q))) h₂ p c)
  , (λ p → closedF H F (λ q → h₁ (there (∈-++⁺ʳ (subsF G F) q))) h₂ p c)
  ]′ (∈-++⁻ (subsF G F) m)

-- ★ `subs T` is closed under the parts a copy or a free calls
closed : ∀ T {T′ C} → T′ ∈ subs T → C ∈ comps T′ → C ∈ subs T
closed (A ⊗t B) (here refl) (here refl)         = there (here refl)
closed (A ⊗t B) (here refl) (there (here refl)) = there (∈-++⁺ʳ (subs A) (here refl))
closed (A ⊗t B) (here refl) (there (there ()))
closed (A ⊕t B) (here refl) (here refl)         = there (here refl)
closed (A ⊕t B) (here refl) (there (here refl)) = there (∈-++⁺ʳ (subs A) (here refl))
closed (A ⊕t B) (here refl) (there (there ()))
closed (Ct l X) (here refl) (here refl)         = there (here refl)
closed (Ct l X) (here refl) (there ())
closed (μt F)   (here refl) (here refl)         = there (here refl)
closed (μt F)   (here refl) (there ())
closed One          (here refl) ()
closed Zero         (here refl) ()
closed (Fn k g A B) (here refl) ()
closed (Nu F)       (here refl) ()
closed (Bt b)       (here refl) ()
closed (A ⊗t B) (there m) c =
  [ (λ p → there (∈-++⁺ˡ (closed A p c))) , (λ p → there (∈-++⁺ʳ (subs A) (closed B p c))) ]′ (∈-++⁻ (subs A) m)
closed (A ⊕t B) (there m) c =
  [ (λ p → there (∈-++⁺ˡ (closed A p c))) , (λ p → there (∈-++⁺ʳ (subs A) (closed B p c))) ]′ (∈-++⁻ (subs A) m)
closed (Ct l X) (there m) c = there (closed X m c)
closed (μt F)   (there m) c = closedF F F there (λ p → p) m c
closed One          (there ())
closed Zero         (there ())
closed (Fn k g A B) (there ())
closed (Nu F)       (there ())
closed (Bt b)       (there ())

------------------------------------------------------------------------
-- 2. WHAT A PROGRAM NAMES: keys, copy/free roots, ν seeds, observers.
------------------------------------------------------------------------

AKey : Set
AKey = Σ BSig Key

-- a table, at its labels (an observer's: `kobs` is compiled at it)
DS : Set
DS = Σ Cx Defs

-- a ν's functor and seed type
NS : Set
NS = LF × LTy

-- a collection, as the tree of where it came from (so a part of it is
-- found by its shape)
infixr 5 _⊹_
data Got : Set where
  ∅   : Got
  k!  : AKey → Got
  t!  : LTy → Got
  c!  : LTy → Got   -- ★ D486: a type a CELL holds (also copied or freed: one of `ts`)
  n!  : NS → Got
  o!  : DS → Got
  p!  : Sig → Got
  -- ★ D498: a many-use closure's LENT entry, at the closure's type: in the universe only
  -- where a lent call can reach that type (`Lent`)
  l!  : LTy → AKey → Got
  -- ★ D498: a lent call through a code word at a closure type, in the block's own code;
  -- a many-use closure's lent body, its own lent calls guarded by the closure's type; a block
  -- that exists whatever the guard (an owned body, a fold's algebra, an observation)
  b!  : LTy → Got
  ?!  : LTy → Got → Got
  !!  : Got → Got
  -- (only its lent calls, at no guard: an owned entry's, whose names its body's already are)
  #!  : Got → Got
  _⊹_ : Got → Got → Got

ks : Got → List AKey
ks (k! κ)  = κ ∷ []
ks (G ⊹ H) = ks G ++ ks H
ks (?! _ G) = ks G
ks (!! G)   = ks G
{-# CATCHALL #-}
ks _       = []

ts : Got → List LTy
ts (t! T)  = T ∷ []
ts (c! T)  = T ∷ []
ts (G ⊹ H) = ts G ++ ts H
ts (?! _ G) = ts G
ts (!! G)   = ts G
{-# CATCHALL #-}
ts _       = []

-- ★ D486: the types cells hold (a closure's environment): their copy and free trampolines are live
cs : Got → List LTy
cs (c! T)  = T ∷ []
cs (G ⊹ H) = cs G ++ cs H
cs (?! _ G) = cs G
cs (!! G)   = cs G
{-# CATCHALL #-}
cs _       = []

cs⊆ts : ∀ G → cs G ⊆ ts G
cs⊆ts ∅       ()
cs⊆ts (k! _)  ()
cs⊆ts (t! _)  ()
cs⊆ts (c! T)  m = m
cs⊆ts (n! _)  ()
cs⊆ts (o! _)  ()
cs⊆ts (p! _)  ()
cs⊆ts (l! _ _) ()
cs⊆ts (G ⊹ H) m = [ (λ p → ∈-++⁺ˡ (cs⊆ts G p)) , (λ p → ∈-++⁺ʳ (ts G) (cs⊆ts H p)) ]′ (∈-++⁻ (cs G) m)
cs⊆ts (?! _ G) m = cs⊆ts G m
cs⊆ts (!! G) m   = cs⊆ts G m
cs⊆ts (b! _) ()
cs⊆ts (#! _) ()

-- ★ D498: the lent entries a collection names, at their closures' types; those at a lent-called type
lentsOf : Got → List (LTy × AKey)
lentsOf (l! T κ) = (T , κ) ∷ []
lentsOf (G ⊹ H)  = lentsOf G ++ lentsOf H
lentsOf (?! _ G) = lentsOf G
lentsOf (!! G)   = lentsOf G
{-# CATCHALL #-}
lentsOf _        = []

lks : (LTy → Bool) → Got → List AKey
lks lc (l! T κ) = if lc T then κ ∷ [] else []
lks lc (G ⊹ H)  = lks lc G ++ lks lc H
lks lc (?! _ G) = lks lc G
lks lc (!! G)   = lks lc G
{-# CATCHALL #-}
lks lc _        = []

lks-∈ : ∀ lc G {T κ} → (T , κ) ∈ lentsOf G → lc T ≡ true → κ ∈ lks lc G
lks-∈ lc (l! T κ) (here refl) e = subst (λ b → κ ∈ (if b then κ ∷ [] else [])) (sym e) (here refl)
lks-∈ lc (G ⊹ H) m e = [ (λ p → ∈-++⁺ˡ (lks-∈ lc G p e)) , (λ p → ∈-++⁺ʳ (lks lc G) (lks-∈ lc H p e)) ]′ (∈-++⁻ (lentsOf G) m)
lks-∈ lc (?! _ G) m e = lks-∈ lc G m e
lks-∈ lc (!! G) m e   = lks-∈ lc G m e

-- what holds of every lent entry holds of those at a lent-called type
lks-All : ∀ {P : AKey → Set} lc G → All (λ p → lc (proj₁ p) ≡ true → P (proj₂ p)) (lentsOf G) → All P (lks lc G)
lks-All {P} lc (l! T κ) (p ∷ []) = by (lc T) refl
  where
    by : ∀ b → lc T ≡ b → All P (if b then κ ∷ [] else [])
    by true  e = p e ∷ []
    by false e = []
lks-All lc (G ⊹ H) a = ++⁺ (lks-All lc G (++⁻ˡ (lentsOf G) a)) (lks-All lc H (++⁻ʳ (lentsOf G) a))
lks-All lc (?! _ G) a = lks-All lc G a
lks-All lc (!! G) a   = lks-All lc G a
lks-All lc (b! _) a   = []
lks-All lc (#! _) a   = []
lks-All lc ∅ a       = []
lks-All lc (k! _) a  = []
lks-All lc (t! _) a  = []
lks-All lc (c! _) a  = []
lks-All lc (n! _) a  = []
lks-All lc (o! _) a  = []
lks-All lc (p! _) a  = []

ns : Got → List NS
ns (n! n)  = n ∷ []
ns (G ⊹ H) = ns G ++ ns H
ns (?! _ G) = ns G
ns (!! G)   = ns G
{-# CATCHALL #-}
ns _       = []

os : Got → List DS
os (o! d)  = d ∷ []
os (G ⊹ H) = os G ++ os H
os (?! _ G) = os G
os (!! G)   = os G
{-# CATCHALL #-}
os _       = []

ps : Got → List Sig
ps (p! s)  = s ∷ []
ps (G ⊹ H) = ps G ++ ps H
ps (?! _ G) = ps G
ps (!! G)   = ps G
{-# CATCHALL #-}
ps _       = []

-- ★ D498: a collection's lent calls, each under the guard it is in (a lent body's own
-- calls under its closure's type, a block that exists regardless under none)
lentCalls : Maybe LTy → Got → List Fact
lentCalls c (b! T)   = (c , T) ∷ []
lentCalls c (?! S G) = lentCalls (just S) G
lentCalls c (!! G)   = lentCalls nothing G
lentCalls c (#! G)   = lentCalls nothing G
lentCalls c (G ⊹ H)  = lentCalls c G ++ lentCalls c H
{-# CATCHALL #-}
lentCalls c _        = []

-- a guard holds under a test
holdsB : Maybe LTy → (LTy → Bool) → Bool
holdsB nothing  lc = true
holdsB (just S) lc = lc S

-- a fact under one guard is the same fact under another, or its own (it was guarded inside)
lentCalls-move : ∀ c₁ c₂ G {d T} → (d , T) ∈ lentCalls c₁ G → (d ≡ c₁ × (c₂ , T) ∈ lentCalls c₂ G) ⊎ ((d , T) ∈ lentCalls c₂ G)
lentCalls-move c₁ c₂ (b! T) (here refl) = inj₁ (refl , here refl)
lentCalls-move c₁ c₂ (?! S G) m = inj₂ m
lentCalls-move c₁ c₂ (!! G) m   = inj₂ m
lentCalls-move c₁ c₂ (#! G) m   = inj₂ m
lentCalls-move c₁ c₂ (G ⊹ H) m =
  [ (λ p → [ (λ { (e , q) → inj₁ (e , ∈-++⁺ˡ q) }) , (λ q → inj₂ (∈-++⁺ˡ q)) ]′ (lentCalls-move c₁ c₂ G p))
  , (λ p → [ (λ { (e , q) → inj₁ (e , ∈-++⁺ʳ (lentCalls c₂ G) q) }) , (λ q → inj₂ (∈-++⁺ʳ (lentCalls c₂ G) q)) ]′ (lentCalls-move c₁ c₂ H p))
  ]′ (∈-++⁻ (lentCalls c₁ G) m)

-- the owned entry's own lent calls, as a collection
blist : List LTy → Got
blist []       = ∅
blist (T ∷ ts) = b! T ⊹ blist ts

-- the program's lent-called types: the least set closed under its facts (`Lent`)
-- (every ν's observation applies its coalgebra lent: its type is lent-called)
obsFacts : List NS → List Fact
obsFacts []             = []
obsFacts ((F , S) ∷ n)  = (nothing , Coalg F S) ∷ obsFacts n

factsOf : Got → List Fact
factsOf g = lentCalls nothing g ++ obsFacts (ns g)

lcOf : Got → LTy → Bool
lcOf g T = elemT T (lentTys (factsOf g))

-- the two spellings of a guard holding agree
holds-eq : ∀ c L → holdsB c (λ T → elemT T L) ≡ holds c L
holds-eq nothing  L = refl
holds-eq (just S) L = refl

-- a ν's coalgebra type is among the observation facts
obsF-∈ : ∀ {F S} ns → (F , S) ∈ ns → (nothing , Coalg F S) ∈ obsFacts ns
obsF-∈ ((F , S) ∷ n) (here refl) = here refl
obsF-∈ (_ ∷ n) (there m)         = there (obsF-∈ n m)

-- a term's: what its code calls by name, the types it copies or frees, the
-- ν's it builds, the tables it observes at; a closure's body with it
tmGot : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Got
-- ★ D498: a many-use closure's OWNED entry's names, by its certificate (`ownT-got`: its term's)
tmGotO : ∀ {Γ} → Defs Γ → ∀ {X A B} (b : Tm Γ X A B) → Own b → Got
tmGot ds (f ∘l g)            = tmGot ds f ⊹ tmGot ds g
tmGot ds (f ⊗l g)            = tmGot ds f ⊹ tmGot ds g
tmGot ds (lcase f g)         = tmGot ds f ⊹ tmGot ds g
tmGot ds (lcata F alg)       = k! (_ , kfold ds F alg) ⊹ !! (tmGot ds alg)
tmGot ds (liter f φ)         = tmGot ds f
tmGot ds (lapp p)            = k! (_ , key1 ds p)
tmGot ds (lend b)            = tmGot ds b
tmGot ds (blift f)           = tmGot ds f
tmGot ds (bfst f)            = tmGot ds f
tmGot ds (bsnd f)            = tmGot ds f
tmGot ds (bcaseE f g)        = tmGot ds f ⊹ tmGot ds g
tmGot ds (bout f)            = tmGot ds f
tmGot ds (bcopy {E = E})     = t! E
tmGot ds (bapp p)            = k! (_ , keyω ds p)
tmGot ds (bev {g = g} {A} {B}) = b! (Fn many g A B)
tmGot ds (dup {A = A})       = t! A
tmGot ds (drop {A = A})      = t! A
tmGot ds (llam {X = X} b γ)  = k! (_ , kbody1 ds b γ) ⊹ c! X ⊹ !! (tmGot ds b)
tmGot ds (llamω {g = g} {X = X} {A} {B} b γ) =
  l! (Fn many g A B) (_ , kbodyω ds b γ) ⊹ c! X ⊹ ?! (Fn many g A B) (tmGot ds b)
  ⊹ k! (_ , kbody1 ds (ownω b) (own-gdb b γ)) ⊹ #! (tmGotO ds b (ownOf b))
-- (D480: a many-use closure also names its owned body, its owned entry's)
tmGot ds (llamωᶜ {g = g} {X = X} {A} {B} b₀ γ) =
  l! (Fn many g A B) (_ , kbodyω ds (cin b₀) (cin-gd b₀ γ)) ⊹ c! X ⊹ !! (tmGot ds b₀) ⊹ k! (_ , kbody1 ds b₀ γ)
tmGot ds (lunf {F = F} {S})  = n! (F , S) ⊹ o! (_ , ε)
tmGot ds (lout {F = F})      = o! (_ , ε)
tmGot ds (lop s)             = p! s
{-# CATCHALL #-}
tmGot ds _                   = ∅
tmGotO ds {X} b o-bg          = (∅ ⊹ (t! X ⊹ ∅)) ⊹ tmGot ds b
tmGotO ds _ o-ev              = ∅
tmGotO ds (bfst {E₂ = X₂} f) (o-fst o) = tmGotO ds f o ⊹ ((∅ ⊹ (∅ ⊹ t! X₂)) ⊹ ∅)
tmGotO ds (bsnd {E₁ = X₁} f) (o-snd o) = tmGotO ds f o ⊹ ((∅ ⊹ (t! X₁ ⊹ ∅)) ⊹ ∅)
tmGotO ds (bfst f ∘l bsnd g) (o-split p q) = tmGotO ds f p ⊹ ((∅ ⊹ tmGotO ds g q) ⊹ ∅)
tmGotO ds (lcase f g) (o-case p q) = (tmGotO ds f p ⊹ tmGotO ds g q) ⊹ ∅
tmGotO ds ((bfst f ⊗l bsnd g) ∘l s) (o-fork p q) =
  (tmGotO ds f p ⊹ tmGotO ds g q) ⊹ ((∅ ⊹ ((∅ ⊹ (∅ ⊹ ((∅ ⊹ ∅) ⊹ ∅))) ⊹ ∅)) ⊹ tmGot ds s)
tmGotO ds (blift g ∘l t) (o-lift p) = tmGot ds g ⊹ tmGotO ds t p
tmGotO ds (t ∘l blift f) (o-pre p)  = tmGotO ds t p ⊹ (∅ ⊹ tmGot ds f)

-- the owned entry's names are its term's
ownT-got : ∀ {Γ} (ds : Defs Γ) {X A B} {b : Tm Γ X A B} (o : Own b) → tmGot ds (ownT o) ≡ tmGotO ds b o
ownT-got ds o-bg          = refl
ownT-got ds o-ev          = refl
ownT-got ds (o-fst o)     = cong (_⊹ _) (ownT-got ds o)
ownT-got ds (o-snd o)     = cong (_⊹ _) (ownT-got ds o)
ownT-got ds (o-split p q) = cong₂ (λ x y → x ⊹ ((∅ ⊹ y) ⊹ ∅)) (ownT-got ds p) (ownT-got ds q)
ownT-got ds (o-case p q)  = cong₂ (λ x y → (x ⊹ y) ⊹ ∅) (ownT-got ds p) (ownT-got ds q)
ownT-got ds (o-fork p q)  = cong₂ (λ x y → (x ⊹ y) ⊹ _) (ownT-got ds p) (ownT-got ds q)
ownT-got ds (o-lift p)    = cong (_ ⊹_) (ownT-got ds p)
ownT-got ds (o-pre p)     = cong (_⊹ _) (ownT-got ds p)

-- a table's: each body's key and what the body names, at its own prefix
defsGot : ∀ {Γ} → Defs Γ → Got
defsGot ε                = ∅
defsGot (ds ▸ b1 b γ)    = defsGot ds ⊹ k! (_ , kbody1 ds b γ) ⊹ tmGot ds b
defsGot (ds ▸ bω b γ)    = defsGot ds ⊹ k! (_ , kbodyω ds b γ) ⊹ tmGot ds b

-- a ν's cell holds its coalgebra and its seed
cty : NS → LTy
cty (F , S) = Coalg F S ⊗t S

------------------------------------------------------------------------
-- 3. ★ THE UNIVERSE: a collection's keys, every copy/free of its types'
-- parts, every observer at every seed. A list: finite by construction.
------------------------------------------------------------------------

kc : LTy → AKey
kc T = _ , kcopy T

kf : LTy → AKey
kf T = _ , kfree T

obsK : List DS → List NS → List AKey
obsK os ns = cmap (λ d → map (λ n → _ , kobs (proj₂ d) (proj₁ n) (proj₂ n)) ns) os

-- the closed universe of a collection: its types closed under `comps`, a
-- ν's cell type among them
record Univ : Set where
  constructor univ′
  field
    keys : List AKey
    tys  : List LTy
    nus  : List NS
    obs  : List DS
    ops  : List Sig
    -- ★ D486: the types cells hold (each among `tys`)
    cts  : List LTy
    cts⊆ : ∀ {T} → T ∈ cts → T ∈ tys
    -- (D493: closed under a copy's or a free's parts, for any universe built by `close`)
    tys-cl : ∀ {T} → T ∈ tys → comps T ⊆ tys
    -- ★ D498: the lent-called closure types (`Lent`): a lent entry is a key only at one
    lct : LTy → Bool
open Univ

-- a collection's cell types: its closures' environments, its ν's contents
close-cts : ∀ g {T} → T ∈ cs g ++ map cty (ns g) → T ∈ cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)
close-cts g m =
  [ (λ p → ∈-++⁺ˡ (∈-cmap⁺ (ts g) (cs⊆ts g p) (here refl)))
  , (λ p → let (n , q , e) = ∈-map⁻ cty p in ∈-++⁺ʳ (cmap subs (ts g)) (∈-cmap⁺ (ns g) q (here e)))
  ]′ (∈-++⁻ (cs g) m)

-- ★ D487: a list of types without repeats (by `TyEq.eqT`), so a type has one copy block, one free
-- block, and a cell type one pair of trampolines, however often the program mentions it
dd : List LTy → List LTy
dd = deduplicateᵇ eqT

private
  fromT : ∀ b → Data.Bool.T b → b ≡ true
  fromT true _ = refl

  dd-resp : ∀ {z x y} → Data.Bool.T (eqT y x) → z ≡ x → z ≡ y
  dd-resp {x = x} {y} t e = trans e (sym (eqT-ok y x (fromT (eqT y x) t)))

  f≢t : false ≡ true → ⊥
  f≢t ()

dd⁺ : ∀ {A xs} → A ∈ xs → A ∈ dd xs
dd⁺ = Data.List.Membership.Setoid.Properties.∈-deduplicate⁺ (setoid LTy) (λ x y → T? (eqT x y)) dd-resp

dd⁻ : ∀ xs {A} → A ∈ dd xs → A ∈ xs
dd⁻ = ∈-deduplicate⁻ (λ x y → T? (eqT x y))

-- ★ D487: a type's place in a list, FOUND: its first equal entry. What the compiler runs is the
-- search; the witness that the type is there is read only where the search would fail, so it is
-- never computed (a membership built through deduplication would be; performance-patterns B2)
private
  drop-here : ∀ {A x} {xs : List LTy} → (A ≡ x → false ≡ true) → A ∈ x ∷ xs → A ∈ xs
  drop-here c (here e)  = ⊥-elim (f≢t (c e))
  drop-here c (there w) = w

  find-step : ∀ {A x} {xs : List LTy} b → (b ≡ true → A ≡ x) → (A ≡ x → b ≡ true)
            → (A ∈ xs → A ∈ xs) → A ∈ x ∷ xs → A ∈ x ∷ xs
  find-step true  ok c k w = here (ok refl)
  find-step false ok c k w = there (k (drop-here c w))

find : ∀ A (xs : List LTy) → A ∈ xs → A ∈ xs
find A []       ()
find A (x ∷ xs) w = find-step (eqT A x) (eqT-ok A x) (λ e → subst (λ y → eqT A y ≡ true) e (eqT-refl A)) (find A xs) w

-- ★ D487: the universe from its lists, the deduplicated ones passed once (computed once, shared by
-- the fields and by `cts⊆`'s search; performance-patterns B1); `R` and `C`, the raw lists, only
-- in the witness
-- (opaque: a universe is compared field by field; this witness is never computed)
opaque
  dd-cl : ∀ (R C D : List LTy) → dd (R ++ C) ≡ D → (∀ {T} → T ∈ R ++ C → comps T ⊆ R ++ C)
        → ∀ {T} → T ∈ D → comps T ⊆ D
  dd-cl R C D eD cl {T} m {C′} c = find C′ D (subst (λ Z → C′ ∈ Z) eD (dd⁺ (cl (dd⁻ (R ++ C) (subst (λ Z → T ∈ Z) (sym eD) m)) c)))

closeD : List AKey → (D : List LTy) → List NS → List DS → List Sig → (Cd : List LTy)
       → (R C : List LTy) → dd (R ++ C) ≡ D → dd C ≡ Cd → (∀ {T} → T ∈ R ++ C → comps T ⊆ R ++ C) → (LTy → Bool) → Univ
closeD K D N O P Cd R C eD eC cl lc =
  univ′ K D N O P Cd (λ {T} m → find T D (subst (λ Z → T ∈ Z) eD (dd⁺ (∈-++⁺ʳ R (dd⁻ C (subst (λ Z → T ∈ Z) (sym eC) m))))))
    (dd-cl R C D eD cl) lc

-- a collection's types, closed under the parts (the raw lists of `close`; sealed, performance-patterns A8)
opaque
  rg-cl : ∀ g {T} → T ∈ cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)
        → comps T ⊆ cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)
  rg-cl g {T} m c =
    [ (λ p → let (R , r , q) = ∈-cmap⁻ (ts g) p in ∈-++⁺ˡ (∈-cmap⁺ (ts g) r (closed R q c)))
    , (λ p → let (n , r , q) = ∈-cmap⁻ (ns g) p in ∈-++⁺ʳ (cmap subs (ts g)) (∈-cmap⁺ (ns g) r (closed (cty n) q c)))
    ]′ (∈-++⁻ (cmap subs (ts g)) m)

  rgc-cl : ∀ g {T} → T ∈ (cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) ++ (cs g ++ map cty (ns g))
         → comps T ⊆ (cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) ++ (cs g ++ map cty (ns g))
  rgc-cl g {T} m c =
    [ (λ p → ∈-++⁺ˡ (rg-cl g p c)) , (λ p → ∈-++⁺ˡ (rg-cl g (close-cts g p) c)) ]′
      (∈-++⁻ (cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) m)

close : (LTy → Bool) → Got → Univ
close lc g = closeD (ks g ++ lks lc g) (dd ((cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) ++ (cs g ++ map cty (ns g))))
                 (ns g) ((_ , ε) ∷ os g) (ps g) (dd (cs g ++ map cty (ns g)))
                 (cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) (cs g ++ map cty (ns g)) refl refl (rgc-cl g) lc

allK : Univ → List AKey
allK U = keys U ++ map kc (tys U) ++ map kf (tys U) ++ obsK (obs U) (nus U)

-- a program's: its table's and its main term's
univ : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Univ
univ ds f = close (lcOf (defsGot ds ⊹ tmGot ds f)) (defsGot ds ⊹ tmGot ds f)

module In (U : Univ) where

  inK : ∀ {κ} → κ ∈ keys U → κ ∈ allK U
  inK = ∈-++⁺ˡ

  inC : ∀ {T} → T ∈ tys U → kc T ∈ allK U
  inC m = ∈-++⁺ʳ (keys U) (∈-++⁺ˡ (∈-map⁺ kc m))

  inF : ∀ {T} → T ∈ tys U → kf T ∈ allK U
  inF m = ∈-++⁺ʳ (keys U) (∈-++⁺ʳ (map kc (tys U)) (∈-++⁺ˡ (∈-map⁺ kf m)))

  inO : ∀ {Γ} {ds : Defs Γ} {F S} → (Γ , ds) ∈ obs U → (F , S) ∈ nus U → (_ , kobs ds F S) ∈ allK U
  inO {ds = ds} {F} {S} d n =
    ∈-++⁺ʳ (keys U) (∈-++⁺ʳ (map kc (tys U)) (∈-++⁺ʳ (map kf (tys U))
      (∈-cmap⁺ (obs U) d (∈-map⁺ (λ n → _ , kobs ds (proj₁ n) (proj₂ n)) n))))

  -- a collection inside the universe, its own lent calls under the guard `c₀` (D498)
  record _⊑[_] (G : Got) (c₀ : Maybe LTy) : Set where
    constructor sub
    field
      gk : ks G ⊆ keys U
      gt : ts G ⊆ tys U
      gn : ns G ⊆ nus U
      go : os G ⊆ obs U
      gp : ps G ⊆ ops U
      gc : cs G ⊆ cts U
      -- ★ D498: a lent entry at a lent-called type is a key
      gl : ∀ {T κ} → (T , κ) ∈ lentsOf G → lct U T ≡ true → κ ∈ keys U
      -- ★ D498: a lent call whose guard holds is at a lent-called type
      gb : ∀ {c T} → (c , T) ∈ lentCalls c₀ G → holdsB c (lct U) ≡ true → lct U T ≡ true
  open _⊑[_]

  -- …at no guard: a block's own code
  _⊑U : Got → Set
  G ⊑U = G ⊑[ nothing ]

  ⊹ˡ : ∀ {G H c₀} → (G ⊹ H) ⊑[ c₀ ] → G ⊑[ c₀ ]
  ⊹ˡ (sub a b c d p e l w) = sub (λ m → a (∈-++⁺ˡ m)) (λ m → b (∈-++⁺ˡ m)) (λ m → c (∈-++⁺ˡ m)) (λ m → d (∈-++⁺ˡ m)) (λ m → p (∈-++⁺ˡ m))
                           (λ m → e (∈-++⁺ˡ m)) (λ m → l (∈-++⁺ˡ m)) (λ m → w (∈-++⁺ˡ m))

  ⊹ʳ : ∀ {G H c₀} → (G ⊹ H) ⊑[ c₀ ] → H ⊑[ c₀ ]
  ⊹ʳ {G} {c₀ = c₀} (sub a b c d p e l w) =
    sub (λ m → a (∈-++⁺ʳ (ks G) m)) (λ m → b (∈-++⁺ʳ (ts G) m)) (λ m → c (∈-++⁺ʳ (ns G) m)) (λ m → d (∈-++⁺ʳ (os G) m))
        (λ m → p (∈-++⁺ʳ (ps G) m)) (λ m → e (∈-++⁺ʳ (cs G) m)) (λ m → l (∈-++⁺ʳ (lentsOf G) m)) (λ m → w (∈-++⁺ʳ (lentCalls c₀ G) m))

  ⊹-join : ∀ {G H c₀} → G ⊑[ c₀ ] → H ⊑[ c₀ ] → (G ⊹ H) ⊑[ c₀ ]
  ⊹-join {G} {c₀ = c₀} (sub a b c d p e l w) (sub a′ b′ c′ d′ p′ e′ l′ w′) =
    sub (λ m → [ a , a′ ] (∈-++⁻ (ks G) m)) (λ m → [ b , b′ ] (∈-++⁻ (ts G) m))
        (λ m → [ c , c′ ] (∈-++⁻ (ns G) m)) (λ m → [ d , d′ ] (∈-++⁻ (os G) m)) (λ m → [ p , p′ ] (∈-++⁻ (ps G) m))
        (λ m → [ e , e′ ] (∈-++⁻ (cs G) m)) (λ m → [ l , l′ ] (∈-++⁻ (lentsOf G) m)) (λ m → [ w , w′ ] (∈-++⁻ (lentCalls c₀ G) m))
    where
      [_,_] : ∀ {X Y Z : Set} → (X → Z) → (Y → Z) → X ⊎ Y → Z
      [ f , g ] (inj₁ x) = f x
      [ f , g ] (inj₂ y) = g y

  ∅⊑ : ∀ {c₀} → ∅ ⊑[ c₀ ]
  ∅⊑ = sub (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

  -- a cell type is a copied and freed type
  ct⊑ : ∀ {X c₀ c₁} → c! X ⊑[ c₀ ] → t! X ⊑[ c₁ ]
  ct⊑ g = sub (λ ()) (λ { (here refl) → cts⊆ U (gc g (here refl)) ; (there ()) }) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

  -- a type among the universe's is a copied and freed type; so are its parts
  ty⊑ : ∀ {T c₀} → T ∈ tys U → t! T ⊑[ c₀ ]
  ty⊑ p = sub (λ ()) (λ { (here refl) → p ; (there ()) }) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

  -- ★ D498: a block that exists regardless: its own calls at no guard
  !!-⊑ : ∀ {G c₀} → (!! G) ⊑[ c₀ ] → G ⊑U
  !!-⊑ (sub a b c d p e l w) = sub a b c d p e l w

  -- a lent body: its own calls under its closure's type
  ?!-⊑ : ∀ {S G c₀} → (?! S G) ⊑[ c₀ ] → G ⊑[ just S ]
  ?!-⊑ (sub a b c d p e l w) = sub a b c d p e l w

  -- …which holds where that type is lent-called
  unguard : ∀ {S G} → G ⊑[ just S ] → lct U S ≡ true → G ⊑U
  unguard {S} {G} (sub a b c d p e l w) eS = sub a b c d p e l by
    where
      by : ∀ {c T} → (c , T) ∈ lentCalls nothing G → holdsB c (lct U) ≡ true → lct U T ≡ true
      by {c} {T} m h = [ (λ { (refl , q) → w q eS }) , (λ q → w q h) ]′ (lentCalls-move nothing (just S) G m)

  -- a lent call at a lent-called type
  b!-⊑ : ∀ {T c₀} → lct U T ≡ true → (b! T) ⊑[ c₀ ]
  b!-⊑ e = sub (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ { (here refl) h → e })

  tyL : ∀ {X₁ X₂ c₀} → t! (X₁ ⊗t X₂) ⊑[ c₀ ] → t! X₁ ⊑[ c₀ ]
  tyL g = ty⊑ (tys-cl U (gt g (here refl)) (here refl))

  tyR : ∀ {X₁ X₂ c₀} → t! (X₁ ⊗t X₂) ⊑[ c₀ ] → t! X₂ ⊑[ c₀ ]
  tyR g = ty⊑ (tys-cl U (gt g (here refl)) (there (here refl)))

  -- ★ D493: a body's owned form needs what the body needs, and the frees of the
  -- environment's parts it drops (sealed: evidence in types, performance-patterns A3)
  opaque
   own-got : ∀ {Γ} {ds : Defs Γ} {X A B c₀} {b : Tm Γ X A B} (o : Own b) → tmGot ds b ⊑[ c₀ ] → t! X ⊑[ c₀ ] → tmGot ds (ownT o) ⊑[ c₀ ]
   own-got o-bg          gb tX = ⊹-join (⊹-join ∅⊑ (⊹-join tX ∅⊑)) gb
   own-got o-ev          gb tX = ∅⊑
   own-got (o-fst o)     gb tX = ⊹-join (own-got o gb (tyL tX)) (⊹-join (⊹-join ∅⊑ (⊹-join ∅⊑ (tyR tX))) ∅⊑)
   own-got (o-snd o)     gb tX = ⊹-join (own-got o gb (tyR tX)) (⊹-join (⊹-join ∅⊑ (⊹-join (tyL tX) ∅⊑)) ∅⊑)
   own-got (o-split p q) gb tX = ⊹-join (own-got p (⊹ˡ gb) (tyL tX)) (⊹-join (⊹-join ∅⊑ (own-got q (⊹ʳ gb) (tyR tX))) ∅⊑)
   own-got (o-case p q)  gb tX = ⊹-join (⊹-join (own-got p (⊹ˡ gb) tX) (own-got q (⊹ʳ gb) tX)) ∅⊑
   own-got (o-fork p q)  gb tX =
     ⊹-join (⊹-join (own-got p (⊹ˡ (⊹ˡ gb)) (tyL tX)) (own-got q (⊹ʳ (⊹ˡ gb)) (tyR tX)))
            (⊹-join (⊹-join ∅⊑ (⊹-join (⊹-join ∅⊑ (⊹-join ∅⊑ (⊹-join (⊹-join ∅⊑ ∅⊑) ∅⊑))) ∅⊑)) (⊹ʳ gb))
   own-got (o-lift p)    gb tX = ⊹-join (⊹ˡ gb) (own-got p (⊹ʳ gb) tX)
   own-got (o-pre p)     gb tX = ⊹-join (own-got p (⊹ˡ gb) tX) (⊹-join ∅⊑ (⊹ʳ gb))

  -- ★ D498: the owned entry at no guard: its names from its body's (any guard), its own lent
  -- calls from the facts-only collection the closure names (`#!`, `ownT-got`)
  ownBody-⊑ : ∀ {Γ} {ds : Defs Γ} {X A B c₀ c₁} {b : Tm Γ X A B} (o : Own b) → tmGot ds b ⊑[ c₀ ] → t! X ⊑[ c₀ ]
            → (#! (tmGotO ds b o)) ⊑[ c₁ ] → tmGot ds (ownT o) ⊑U
  ownBody-⊑ {ds = ds} o g tX h =
    sub (gk r) (gt r) (gn r) (go r) (gp r) (gc r) (gl r)
        (λ {c} {T} m e → gb h (subst (λ G → (c , T) ∈ lentCalls nothing G) (ownT-got ds o) m) e)
    where r = own-got o g tX

  inCc : ∀ {T} → T ∈ cts U → kc T ∈ allK U
  inCc m = inC (cts⊆ U m)

  inFc : ∀ {T} → T ∈ cts U → kf T ∈ allK U
  inFc m = inF (cts⊆ U m)

  ----------------------------------------------------------------------
  -- 4. CODE INSIDE THE UNIVERSE: every call, every closure or ν a `prim`
  -- builds, every observation's table.
  ----------------------------------------------------------------------

  PrimIn : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Set
  PrimIn ds (llam {X = X} b γ)  = (_ , kbody1 ds b γ) ∈ allK U × X ∈ cts U
  PrimIn ds (llamω {g = g} {X = X} {A} {B} b γ) =
    (lct U (Fn many g A B) ≡ true → (_ , kbodyω ds b γ) ∈ allK U) × X ∈ cts U × (_ , kbody1 ds (ownω b) (own-gdb b γ)) ∈ allK U
  PrimIn ds (llamωᶜ {g = g} {X = X} {A} {B} b₀ γ) =
    (lct U (Fn many g A B) ≡ true → (_ , kbodyω ds (cin b₀) (cin-gd b₀ γ)) ∈ allK U) × X ∈ cts U × (_ , kbody1 ds b₀ γ) ∈ allK U
  PrimIn ds (lunf {F = F} {S})  = (F , S) ∈ nus U × (_ , ε) ∈ obs U
  PrimIn ds ρl        = ⊤
  PrimIn ds ρl⁻       = ⊤
  PrimIn ds lul       = ⊤
  PrimIn ds lul⁻      = ⊤
  PrimIn ds lassoc    = ⊤
  PrimIn ds lassoc⁻   = ⊤
  PrimIn ds lswap     = ⊤
  PrimIn ds drop      = ⊤
  PrimIn ds linl      = ⊤
  PrimIn ds ldist     = ⊤
  PrimIn ds linr      = ⊤
  PrimIn ds lIn       = ⊤
  PrimIn ds lOutμ     = ⊤
  PrimIn ds (lclo F p) = ⊤
  PrimIn ds (lconst v) = ⊤
  PrimIn ds (lop s)   = s ∈ ops U
  {-# CATCHALL #-}
  PrimIn ds _         = ⊥

  IIn : ∀ {sh sh′} → Insᴵ sh sh′ → Set
  CIn : ∀ {sh T} → Codeᴵ sh T → Set

  IIn (call {σ} κ)   = (σ , κ) ∈ allK U
  IIn (prim ds g)    = PrimIn ds g
  IIn (iobs ds)     = (_ , ε) ∈ obs U
  IIn (loop c)       = CIn c
  -- ★ D498: a lent call through a code word is at a lent-called type (its closure has a lent entry)
  IIn (icallω {g = g} {A} {B}) = lct U (Fn many g A B) ≡ true
  {-# CATCHALL #-}
  IIn _              = ⊤

  CIn end           = ⊤
  CIn (i ⨾ c)       = IIn i × CIn c
  CIn (case c₁ c₂)  = CIn c₁ × CIn c₂
  CIn (ecase c₁ c₂) = CIn c₁ × CIn c₂
  CIn halted        = ⊤

  -- (D484: the right factor of a `⊗l`)
  right-in : ∀ {Γ} (ds : Defs Γ) {E B B′} (h : Tm Γ E B B′) (m : Maybe (IsLid h)) {Es A S T}
             {k : Codeᴵ (E ∷ Es ∣ A ∷ B′ ∷ S) T} → tmGot ds h ⊑U → CIn k → CIn (rightᴵ ds h m k)

  -- ★ a term's code is inside when what it names is
  comp-in : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) {Es S T} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) T}
          → tmGot ds t ⊑U → CIn k → CIn (compᴵ ds t k)
  comp-in ds lid g ck            = ck
  comp-in ds (f ∘l h) g ck       = comp-in ds h (⊹ʳ g) (comp-in ds f (⊹ˡ g) ck)
  comp-in ds (f ⊗l h) g ck       = tt , comp-in ds f (⊹ˡ g) (right-in ds h (isLid? h) (⊹ʳ g) (tt , ck))
  comp-in ds (lcase f h) g ck    = comp-in ds f (⊹ˡ g) ck , comp-in ds h (⊹ʳ g) ck
  comp-in ds (lcata F alg) g ck  = inK (gk g (here refl)) , ck
  comp-in ds (liter f φ) g ck    = comp-in ds f g tt , ck
  comp-in ds (lapp p) g ck       = tt , inK (gk g (here refl)) , ck
  comp-in ds (lend b) g ck       = tt , comp-in ds b g (tt , ck)
  comp-in ds (blift f) g ck      = tt , comp-in ds f g (tt , ck)
  comp-in ds (bfst f) g ck       = tt , comp-in ds f g (tt , ck)
  comp-in ds (bsnd f) g ck       = tt , comp-in ds f g (tt , ck)
  comp-in ds (bcaseE f h) g ck   = comp-in ds f (⊹ˡ g) (tt , ck) , comp-in ds h (⊹ʳ g) (tt , ck)
  comp-in ds (bout f) g ck       = tt , comp-in ds f g (tt , ck)
  comp-in ds bcopy g ck          = inC (gt g (here refl)) , ck
  comp-in ds (bapp p) g ck       = tt , inK (gk g (here refl)) , tt , ck
  comp-in ds ρl g ck             = tt , ck
  comp-in ds ρl⁻ g ck            = tt , ck
  comp-in ds lul g ck            = tt , ck
  comp-in ds lul⁻ g ck           = tt , ck
  comp-in ds lassoc g ck         = tt , ck
  comp-in ds lassoc⁻ g ck        = tt , ck
  comp-in ds lswap g ck          = tt , ck
  comp-in ds dup g ck            = tt , tt , tt , tt , tt , inC (gt g (here refl)) , tt , tt , ck
  comp-in ds drop g ck           = inF (gt g (here refl)) , ck
  comp-in ds linl g ck           = tt , ck
  comp-in ds ldist g ck          = tt , ck
  comp-in ds linr g ck           = tt , ck
  comp-in ds lIn g ck            = tt , ck
  comp-in ds lOutμ g ck          = tt , ck
  comp-in ds (lclo F p) g ck     = tt , ck
  comp-in ds (lconst v) g ck     = tt , ck
  comp-in ds (lop s) g ck        = gp g (here refl) , ck
  comp-in ds lzero g ck          = tt , ck
  comp-in ds (llam b γ) g ck     = (inK (gk g (here refl)) , gc g (∈-++⁺ʳ [] (here refl))) , ck
  comp-in ds (llamω b γ) g ck    = ((λ e → inK (gl g (here refl) e)) , gc g (∈-++⁺ʳ [] (here refl)) , inK (gk (⊹ʳ (⊹ʳ (⊹ʳ g))) (here refl))) , ck
  comp-in ds (llamωᶜ b₀ γ) g ck  = ((λ e → inK (gl g (here refl) e)) , gc g (∈-++⁺ʳ [] (here refl)) , inK (gk (⊹ʳ (⊹ʳ (⊹ʳ g))) (here refl))) , ck
  comp-in ds lev g ck            = tt , ck
  comp-in ds bev g ck            = gb g (here refl) refl , ck
  comp-in ds levω g ck           = tt , (tt , ck)
  comp-in ds lunf g ck           = (gn g (here refl) , go g (here refl)) , ck
  comp-in ds lout g ck           = go g (here refl) , ck

  right-in ds h (just is-lid) g ck = ck
  right-in ds h nothing       g ck = tt , comp-in ds h g (tt , ck)

  ----------------------------------------------------------------------
  -- 5. ★ THE BLOCKS ARE INSIDE: each key's code, from what named it.
  ----------------------------------------------------------------------

  BIn : AKey → Set
  BIn (σ , κ) = CIn (blockᴵ κ)

  travI-in : ∀ {Γ} {ds : Defs Γ} {F E A} {alg : Tm Γ E (LF∙ F A) A} G {Es S T} {k : Codeᴵ (E ∷ Es ∣ LF∙ G A ∷ S) T}
           → (_ , kfold ds F alg) ∈ allK U → CIn k → CIn (travᴵ ds F alg G k)
  travI-in Idf      m ck = m , ck
  travI-in Kone     m ck = ck
  travI-in Kzero    m ck = ck
  travI-in (Kb b)   m ck = ck
  travI-in (Kμ G)   m ck = ck
  travI-in (G ⊕f H) m ck = travI-in G m (tt , ck) , travI-in H m (tt , ck)
  travI-in (G ⊗f H) m ck = tt , travI-in G m (tt , travI-in H m (tt , tt , ck))

  -- a copy or a free of a type is inside when the copies or frees of its parts are
  copy-in : ∀ T → comps T ⊆ tys U → BIn (kc T)
  copy-in One          h = tt
  copy-in Zero         h = tt , tt
  copy-in (A ⊗t B)     h = tt , inC (h (here refl)) , tt , tt , tt , inC (h (there (here refl))) , tt , tt , tt , tt
  copy-in (A ⊕t B)     h = (inC (h (here refl)) , tt , tt , tt) , (inC (h (there (here refl))) , tt , tt , tt)
  copy-in (Bt b)       h = tt , tt
  copy-in (μt F)       h = tt , inC (h (here refl)) , tt , tt , tt
  copy-in (Ct l X)     h = tt , inC (h (here refl)) , tt , tt , tt
  copy-in (Fn k g A B) h = tt , tt
  copy-in (Nu F)       h = tt , tt

  -- ★ D503: a round of a μ's free loop frees the parts before the recursive position:
  -- each a part of the layer, so in the universe (`tys-cl`, again and again)
  peel-in : ∀ {F} G (t : Tail G) {Es S V} {k : Codeᴵ (Es ∣ (One ⊕t μt F) ∷ S) V}
          → LF∙ G (μt F) ∈ tys U → CIn k → CIn (peel G t k)
  peel-in Idf      t-id         m ck = tt , ck
  peel-in Kone     t-one        m ck = tt , ck
  peel-in Kzero    t-zero       m ck = tt , ck
  peel-in (Kb b)   t-b          m ck = inF m , tt , ck
  peel-in (Kμ G)   t-μ          m ck = inF m , tt , ck
  peel-in (G ⊗f H) (t-pair n t) m ck =
    tt , inF (tys-cl U m (here refl)) , tt , tt , peel-in H t (tys-cl U m (there (here refl))) ck
  peel-in (G ⊕f H) (t-sum a b)  m ck = peel-in G a (tys-cl U m (here refl)) ck , peel-in H b (tys-cl U m (there (here refl))) ck

  freeμ-in : ∀ F (t : Maybe (Tail F)) → LF∙ F (μt F) ∈ tys U → CIn (freeμ F t)
  freeμ-in F (just t) m = tt , (tt , peel-in F t m tt) , tt , tt
  freeμ-in F nothing  m = tt , inF m , tt

  free-in : ∀ T → comps T ⊆ tys U → BIn (kf T)
  free-in One          h = tt
  free-in Zero         h = tt , tt
  free-in (A ⊗t B)     h = tt , inF (h (here refl)) , tt , inF (h (there (here refl))) , tt , tt , tt
  free-in (A ⊕t B)     h = (inF (h (here refl)) , tt) , (inF (h (there (here refl))) , tt)
  free-in (Bt b)       h = tt , tt
  free-in (μt F)       h = freeμ-in F (tail? F) (h (here refl))
  free-in (Ct l X)     h = tt , inF (h (here refl)) , tt
  free-in (Fn k g A B) h = tt , tt
  free-in (Nu F)       h = tt , tt

  -- an observation names a copy and a free of the coalgebra, and the ν's it builds
  strL-got : ∀ {Γ} (d : Defs Γ) F G S → Coalg F S ∈ tys U → tmGot d (strL F G S) ⊑U
  strL-got d F Idf      S c = ⊹-join (⊹-join (sub (λ ()) (one c) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())) ∅⊑) ∅⊑
  strL-got d F Kone     S c = ∅⊑
  strL-got d F Kzero    S c = ∅⊑
  strL-got d F (Kb b)   S c = ∅⊑
  strL-got d F (Kμ G)   S c = ∅⊑
  strL-got d F (G ⊕f H) S c = ⊹-join (⊹-join ∅⊑ (strL-got d F G S c)) (⊹-join ∅⊑ (strL-got d F H S c))
  strL-got d F (G ⊗f H) S c = ⊹-join (strL-got d F G S c) (strL-got d F H S c)

  -- ★ D496: the owned form names the coalgebra's free, and the lent form's copies
  dropC-got : ∀ {Γ} (d : Defs Γ) F S → Coalg F S ∈ tys U → (t! (Coalg F S)) ⊑U
  dropC-got d F S c = sub (λ ()) (one c) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

  mutual
    strO-got : ∀ {Γ} (d : Defs Γ) F G S → Coalg F S ∈ tys U → tmGot d (strO F G S) ⊑U
    strO-got d F Idf      S c = ∅⊑
    strO-got d F Kone     S c = ⊹-join ∅⊑ (⊹-join (dropC-got d F S c) ∅⊑)
    strO-got d F Kzero    S c = ⊹-join ∅⊑ (⊹-join (dropC-got d F S c) ∅⊑)
    strO-got d F (Kb b)   S c = ⊹-join ∅⊑ (⊹-join (dropC-got d F S c) ∅⊑)
    strO-got d F (Kμ G)   S c = ⊹-join ∅⊑ (⊹-join (dropC-got d F S c) ∅⊑)
    strO-got d F (G ⊕f H) S c = ⊹-join (⊹-join (⊹-join ∅⊑ (strO-got d F G S c)) (⊹-join ∅⊑ (strO-got d F H S c))) ∅⊑
    strO-got d F (G ⊗f H) S c = strP-got d F G H S (hasId H) c

    strP-got : ∀ {Γ} (d : Defs Γ) F G H S b → Coalg F S ∈ tys U → tmGot d (strP F G H S b) ⊑U
    strP-got d F G H S true  c =
      ⊹-join (⊹-join ∅⊑ (strO-got d F H S c))
             (⊹-join ∅⊑ (⊹-join (⊹-join ∅⊑ ∅⊑) (⊹-join ∅⊑ (⊹-join (strL-got d F G S c) ∅⊑))))
    strP-got d F G H S false c =
      ⊹-join (⊹-join (strO-got d F G S c) ∅⊑) (⊹-join ∅⊑ (⊹-join ∅⊑ (strL-got d F H S c)))

  mapNu-got : ∀ {Γ} (d : Defs Γ) F G S → (F , S) ∈ nus U → (_ , ε) ∈ obs U → tmGot d (mapNu F G S) ⊑U
  mapNu-got d F Idf      S n o = sub (λ ()) (λ ()) (one n) (one o) (λ ()) (λ ()) (λ ()) (λ ())
  mapNu-got d F Kone     S n o = ∅⊑
  mapNu-got d F Kzero    S n o = ∅⊑
  mapNu-got d F (Kb b)   S n o = ∅⊑
  mapNu-got d F (Kμ G)   S n o = ∅⊑
  mapNu-got d F (G ⊕f H) S n o = ⊹-join (⊹-join ∅⊑ (mapNu-got d F G S n o)) (⊹-join ∅⊑ (mapNu-got d F H S n o))
  mapNu-got d F (G ⊗f H) S n o = ⊹-join (mapNu-got d F G S n o) (mapNu-got d F H S n o)

  obs-in : ∀ {Γ} (d : Defs Γ) F S → (F , S) ∈ nus U → Coalg F S ∈ tys U → (_ , ε) ∈ obs U → lct U (Coalg F S) ≡ true
         → BIn (_ , kobs d F S)
  obs-in d F S n c o lC =
    tt , comp-in d (obsT F S)
           (⊹-join (mapNu-got d F F S n o) (⊹-join (strO-got d F F S c) (b!-⊑ lC)))
           (tt , tt)

  -- a body, a fold, a label: inside when what they name is
  body1-in : ∀ {Γ} {ds : Defs Γ} {g X A B} {b : Tm Γ One (X ⊗t A) B} {γ : Gd g b}
           → tmGot ds b ⊑U → BIn (_ , kbody1 ds b γ)
  body1-in {ds = ds} {b = b} g = tt , comp-in ds b g (tt , tt)

  bodyω-in : ∀ {Γ} {ds : Defs Γ} {g X A B} {b : Tm Γ X A B} {γ : Gd g b}
           → tmGot ds b ⊑U → BIn (_ , kbodyω ds b γ)
  bodyω-in {ds = ds} {b = b} g = comp-in ds b g tt

  key1-in : ∀ {Γ} {ds : Defs Γ} {l g X A B} → defsGot ds ⊑U → (p : Γ ∋[ l ] sg once g X A B) → BIn (_ , key1 ds p)
  key1-in {ds = ds ▸ b1 _ _} g (there p) = key1-in (⊹ˡ g) p
  key1-in {ds = ds ▸ bω _ _} g (there p) = key1-in (⊹ˡ g) p
  key1-in {ds = ds ▸ b1 b γ} g here      = body1-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))

  keyω-in : ∀ {Γ} {ds : Defs Γ} {l g X A B} → defsGot ds ⊑U → (p : Γ ∋[ l ] sg many g X A B) → BIn (_ , keyω ds p)
  keyω-in {ds = ds ▸ b1 _ _} g (there p) = keyω-in (⊹ˡ g) p
  keyω-in {ds = ds ▸ bω _ _} g (there p) = keyω-in (⊹ˡ g) p
  keyω-in {ds = ds ▸ bω b γ} g here      = bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))

  -- ★ D488: the same evidence for EVERY key at once, in one pass over the term (what the compiler
  -- runs: a block's evidence is looked up in it, not searched for from its membership proof, which
  -- rebuilt every enclosing subterm's key list per block; docs/performance-patterns.md B1, B2)
  tm-all : ∀ {Γ} {ds : Defs Γ} {E A B c₀} (t : Tm Γ E A B) → defsGot ds ⊑U → tmGot ds t ⊑[ c₀ ] → All BIn (ks (tmGot ds t))
  tm-all (f ∘l h) d g     = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (f ⊗l h) d g     = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (lcase f h) d g  = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (bcaseE f h) d g = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (lcata F alg) d g = (tt , travI-in F (inK (gk g (here refl))) (comp-in _ alg (!!-⊑ (⊹ʳ g)) tt)) ∷ tm-all alg d (!!-⊑ (⊹ʳ g))
  tm-all (liter f φ) d g  = tm-all f d g
  tm-all (lend b) d g     = tm-all b d g
  tm-all (blift f) d g    = tm-all f d g
  tm-all (bfst f) d g     = tm-all f d g
  tm-all (bsnd f) d g     = tm-all f d g
  tm-all (bout f) d g     = tm-all f d g
  tm-all (lapp p) d g     = key1-in d p ∷ []
  tm-all (bapp p) d g     = keyω-in d p ∷ []
  tm-all {ds = ds} (llam b γ) d g = body1-in {ds = ds} {b = b} {γ = γ} (!!-⊑ (⊹ʳ (⊹ʳ g))) ∷ tm-all b d (!!-⊑ (⊹ʳ (⊹ʳ g)))
  tm-all {ds = ds} (llamω b γ) d g =
    ++⁺ (tm-all b d (?!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g)))))
          (body1-in {ds = ds} {b = ownω b} {γ = own-gdb b γ}
             (subst (λ t → tmGot ds t ⊑U) (sym (ownω-≡ b))
                    (ownBody-⊑ (ownOf b) (?!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g)))) (ct⊑ (⊹ˡ (⊹ʳ g))) (⊹ʳ (⊹ʳ (⊹ʳ (⊹ʳ g)))))) ∷ [])
  tm-all {ds = ds} (llamωᶜ b₀ γ) d g =
    ++⁺ (tm-all b₀ d (!!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g))))) (body1-in {ds = ds} {b = b₀} {γ = γ} (!!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g)))) ∷ [])
  tm-all lid d g       = []
  tm-all ρl d g        = []
  tm-all ρl⁻ d g       = []
  tm-all lul d g       = []
  tm-all lul⁻ d g      = []
  tm-all lassoc d g    = []
  tm-all lassoc⁻ d g   = []
  tm-all lswap d g     = []
  tm-all dup d g       = []
  tm-all drop d g      = []
  tm-all linl d g      = []
  tm-all ldist d g     = []
  tm-all linr d g      = []
  tm-all lzero d g     = []
  tm-all lIn d g       = []
  tm-all lOutμ d g     = []
  tm-all (lclo F p) d g = []
  tm-all bcopy d g     = []
  tm-all lev d g       = []
  tm-all bev d g       = []
  tm-all levω d g      = []
  tm-all lunf d g      = []
  tm-all lout d g      = []
  tm-all (lconst v) d g = []
  tm-all (lop s) d g   = []

  defs-all : ∀ {Γ} {ds : Defs Γ} → defsGot ds ⊑U → All BIn (ks (defsGot ds))
  defs-all {ds = ε} g = []
  defs-all {ds = ds ▸ b1 b γ} g =
    ++⁺ (defs-all (⊹ˡ g)) (body1-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g)) ∷ tm-all b (⊹ˡ g) (⊹ʳ (⊹ʳ g)))
  defs-all {ds = ds ▸ bω b γ} g =
    ++⁺ (defs-all (⊹ˡ g)) (bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g)) ∷ tm-all b (⊹ˡ g) (⊹ʳ (⊹ʳ g)))

  -- ★ D498: every lent entry a term names has its block inside (needed only where its type is
  -- lent-called, but inside at any: its body's names are)
  BInL : LTy × AKey → Set
  BInL (T , κ) = lct U T ≡ true → BIn κ

  tm-allL : ∀ {Γ} {ds : Defs Γ} {E A B c₀} (t : Tm Γ E A B) → defsGot ds ⊑U → tmGot ds t ⊑[ c₀ ] → All BInL (lentsOf (tmGot ds t))
  tm-allL (f ∘l h) d g     = ++⁺ (tm-allL f d (⊹ˡ g)) (tm-allL h d (⊹ʳ g))
  tm-allL (f ⊗l h) d g     = ++⁺ (tm-allL f d (⊹ˡ g)) (tm-allL h d (⊹ʳ g))
  tm-allL (lcase f h) d g  = ++⁺ (tm-allL f d (⊹ˡ g)) (tm-allL h d (⊹ʳ g))
  tm-allL (bcaseE f h) d g = ++⁺ (tm-allL f d (⊹ˡ g)) (tm-allL h d (⊹ʳ g))
  tm-allL (lcata F alg) d g = tm-allL alg d (!!-⊑ (⊹ʳ g))
  tm-allL (liter f φ) d g  = tm-allL f d g
  tm-allL (lend b) d g     = tm-allL b d g
  tm-allL (blift f) d g    = tm-allL f d g
  tm-allL (bfst f) d g     = tm-allL f d g
  tm-allL (bsnd f) d g     = tm-allL f d g
  tm-allL (bout f) d g     = tm-allL f d g
  tm-allL (llam b γ) d g   = tm-allL b d (!!-⊑ (⊹ʳ (⊹ʳ g)))
  tm-allL {ds = ds} (llamω b γ) d g =
    (λ e → bodyω-in {ds = ds} {b = b} {γ = γ} (unguard (?!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g)))) e))
    ∷ ++⁺ (tm-allL b d (?!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g))))) []
  tm-allL {ds = ds} (llamωᶜ b₀ γ) d g =
    (λ e → bodyω-in {ds = ds} {b = cin b₀} {γ = cin-gd b₀ γ}
             (⊹-join (!!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g)))) (⊹-join (⊹-join (ct⊑ (⊹ˡ (⊹ʳ g))) ∅⊑) ∅⊑)))
    ∷ ++⁺ (tm-allL b₀ d (!!-⊑ (⊹ˡ (⊹ʳ (⊹ʳ g))))) []
  tm-allL (lapp p) d g     = []
  tm-allL (bapp p) d g     = []
  tm-allL lid d g          = []
  tm-allL ρl d g           = []
  tm-allL ρl⁻ d g          = []
  tm-allL lul d g          = []
  tm-allL lul⁻ d g         = []
  tm-allL lassoc d g       = []
  tm-allL lassoc⁻ d g      = []
  tm-allL lswap d g        = []
  tm-allL dup d g          = []
  tm-allL drop d g         = []
  tm-allL linl d g         = []
  tm-allL ldist d g        = []
  tm-allL linr d g         = []
  tm-allL lzero d g        = []
  tm-allL lIn d g          = []
  tm-allL lOutμ d g        = []
  tm-allL (lclo F p) d g   = []
  tm-allL bcopy d g        = []
  tm-allL lev d g          = []
  tm-allL bev d g          = []
  tm-allL levω d g         = []
  tm-allL lunf d g         = []
  tm-allL lout d g         = []
  tm-allL (lconst v) d g   = []
  tm-allL (lop s) d g      = []

  defs-allL : ∀ {Γ} {ds : Defs Γ} → defsGot ds ⊑U → All BInL (lentsOf (defsGot ds))
  defs-allL {ds = ε} g = []
  defs-allL {ds = ds ▸ b1 b γ} g = ++⁺ (defs-allL (⊹ˡ g)) (tm-allL b (⊹ˡ g) (⊹ʳ (⊹ʳ g)))
  defs-allL {ds = ds ▸ bω b γ} g = ++⁺ (defs-allL (⊹ˡ g)) (tm-allL b (⊹ˡ g) (⊹ʳ (⊹ʳ g)))

  -- those at a lent-called type: the universe's lent keys
  lks-all : ∀ lc → lc ≡ lct U → ∀ G → All BInL (lentsOf G) → All BIn (lks lc G)
  lks-all lc refl G a = lks-All lc G a

  -- a key's evidence, looked up
  lookupA : ∀ {xs : List AKey} → All BIn xs → ∀ {κ} → κ ∈ xs → BIn κ
  lookupA (p ∷ ps) (here refl) = p
  lookupA (p ∷ ps) (there m)   = lookupA ps m

------------------------------------------------------------------------
-- 6. ★ A PROGRAM'S UNIVERSE IS CLOSED: its blocks and its start are inside.
------------------------------------------------------------------------

-- ★ D487: over a universe `V` computed ONCE and shared (a module parameter is an argument at run
-- time, so every use below reads the same lists; a definition under `ds f` would be recomputed at
-- each call: performance-patterns B1). `Program ds f` is this at `univ ds f`, by `refl`.
-- Memberships in the shared lists are FOUND there (`find`); their witnesses, at the program's own
-- universe moved along `eV`, are never computed.
module ProgramW {Γ} (ds : Defs Γ) (f : LTm Γ One One) (V : Univ) (eV : univ ds f ≡ V) where

  g₀ : Got
  g₀ = defsGot ds ⊹ tmGot ds f

  U : Univ
  U = V

  open In U

  -- the raw lists (witnesses only)
  Rt : List LTy
  Rt = cmap subs (ts g₀) ++ cmap (λ n → subs (cty n)) (ns g₀)

  Cl : List LTy
  Cl = cs g₀ ++ map cty (ns g₀)

  -- a membership in the program's own universe, at the shared one, and back
  mv : ∀ {A : Set} {x : A} (sel : Univ → List A) → x ∈ sel (univ ds f) → x ∈ sel U
  mv sel m = subst (λ W → _ ∈ sel W) eV m

  mv⁻ : ∀ {A : Set} {x : A} (sel : Univ → List A) → x ∈ sel U → x ∈ sel (univ ds f)
  mv⁻ sel m = subst (λ W → _ ∈ sel W) (sym eV) m

  -- a type of the closure, found among the shared types
  inT : ∀ {T} → T ∈ Rt ++ Cl → T ∈ tys U
  inT {T} m = find T (tys U) (mv tys (dd⁺ m))

  g₀⊑ : g₀ ⊑U
  g₀⊑ = sub (λ m → mv keys (∈-++⁺ˡ m)) (λ {T} m → inT (∈-++⁺ˡ (∈-++⁺ˡ (∈-cmap⁺ (ts g₀) m (here refl))))) (λ m → mv nus m)
            (λ m → mv obs (there m)) (λ m → mv ops m) (λ {T} m → find T (cts U) (mv cts (dd⁺ (∈-++⁺ˡ m))))
            (λ {T} m e → mv keys (∈-++⁺ʳ (ks g₀) (lks-∈ (lct (univ ds f)) g₀ m (trans (cong (λ W → lct W T) eV) e))))
            (λ {c} {T} m h → subst (λ W → lct W T ≡ true) eV
               (lent-closed (factsOf g₀) (∈-++⁺ˡ m)
                  (trans (sym (holds-eq c (lentTys (factsOf g₀)))) (subst (λ W → holdsB c (lct W) ≡ true) (sym eV) h))))

  -- ★ D498: every ν's coalgebra type is lent-called (its observation applies it lent)
  ns-lent : ∀ {F S} → (F , S) ∈ nus U → lct U (Coalg F S) ≡ true
  ns-lent {F} {S} n = subst (λ W → lct W (Coalg F S) ≡ true) eV
    (lent-closed (factsOf g₀) (∈-++⁺ʳ (lentCalls nothing g₀) (obsF-∈ (ns g₀) (mv⁻ nus n))) refl)

  -- the types are closed under a copy's or a free's parts
  -- the closure's own types (before the cell types)
  tsR : ∀ {T} → T ∈ Rt → comps T ⊆ Rt
  tsR {T} m c =
    [ (λ p → let (R , r , q) = ∈-cmap⁻ (ts g₀) p in ∈-++⁺ˡ (∈-cmap⁺ (ts g₀) r (closed R q c)))
    , (λ p → let (n , r , q) = ∈-cmap⁻ (ns g₀) p in ∈-++⁺ʳ (cmap subs (ts g₀)) (∈-cmap⁺ (ns g₀) r (closed (cty n) q c)))
    ]′ (∈-++⁻ (cmap subs (ts g₀)) m)

  tsW : ∀ {T} → T ∈ Rt ++ Cl → comps T ⊆ Rt ++ Cl
  tsW {T} m c = [ (λ p → ∈-++⁺ˡ (tsR p c)) , (λ p → ∈-++⁺ˡ (tsR (close-cts g₀ p) c)) ]′ (∈-++⁻ Rt m)

  ts-closed : ∀ {T} → T ∈ tys U → comps T ⊆ tys U
  ts-closed {T} m c = inT (tsW (dd⁻ (Rt ++ Cl) (mv⁻ tys m)) c)

  -- a ν's coalgebra type is among them
  ns-coalg : ∀ {F S} → (F , S) ∈ nus U → Coalg F S ∈ tys U
  ns-coalg n = inT (∈-++⁺ˡ (∈-++⁺ʳ (cmap subs (ts g₀)) (∈-cmap⁺ (ns g₀) (mv⁻ nus n) (there (here refl)))))

  -- …and so is its cell's (the coalgebra and the seed: what the lowering lays out)
  -- ★ D486: a ν's cell type is a CELL type (its copy and free trampolines live)
  ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ cts U
  ncty n = find _ (cts U) (mv cts (dd⁺ (∈-++⁺ʳ (cs g₀) (∈-map⁺ cty (mv⁻ nus n)))))

  -- ★ EVERY BLOCK OF THE UNIVERSE IS INSIDE IT
  -- ★ D487: every block's evidence, in one pass (the keys' by `defs-all`/`tm-all`; a type's copy
  -- and free, an observer's, each once), looked up per block
  blocks-all : All BIn (allK U)
  blocks-all =
    ++⁺ (subst (λ W → All BIn (keys W)) eV
           (++⁺ (++⁺ (defs-all (⊹ˡ g₀⊑)) (tm-all f (⊹ˡ g₀⊑) (⊹ʳ g₀⊑)))
                (lks-all (lct (univ ds f)) (cong lct eV) g₀ (++⁺ (defs-allL (⊹ˡ g₀⊑)) (tm-allL f (⊹ˡ g₀⊑) (⊹ʳ g₀⊑))))))
        (++⁺ (map⁺ (tabulate (λ {T} t → copy-in T (ts-closed t))))
             (++⁺ (map⁺ (tabulate (λ {T} t → free-in T (ts-closed t))))
                  (tabulate (λ r → let ((Δ , d) , o , s) = ∈-cmap⁻ (obs U) r
                                       ((F , S) , n , e) = ∈-map⁻ (λ n → _ , kobs d (proj₁ n) (proj₂ n)) s
                                   in subst BIn (sym e) (obs-in d F S n (ns-coalg n) (mv obs (here refl)) (ns-lent n))))))

  -- (opaque: a proof; sealed, two spellings of a block's evidence compare as one stuck term)
  opaque
    blocks-in : ∀ {κ} → κ ∈ allK U → BIn κ
    blocks-in = lookupA blocks-all

  -- ★ and so is the program's start
  start-in : ∀ {Es S T} {k : Codeᴵ (One ∷ Es ∣ One ∷ S) T} → CIn k → CIn (compᴵ ds f k)
  start-in ck = comp-in ds f (⊹ʳ g₀⊑) ck

-- the program's: at its own universe
module Program {Γ} (ds : Defs Γ) (f : LTm Γ One One) = ProgramW ds f (univ ds f) refl
