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
open import Data.Bool using (true; false)
import Data.List.Membership.Setoid.Properties
open import Relation.Nullary.Decidable.Core using (T?)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-deduplicate⁻)
open import Data.List.Relation.Unary.Any using (here; there; toSum)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate)
open import Data.List.Relation.Unary.All.Properties using (++⁺; map⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; setoid)
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
  _⊹_ : Got → Got → Got

ks : Got → List AKey
ks (k! κ)  = κ ∷ []
ks (G ⊹ H) = ks G ++ ks H
{-# CATCHALL #-}
ks _       = []

ts : Got → List LTy
ts (t! T)  = T ∷ []
ts (c! T)  = T ∷ []
ts (G ⊹ H) = ts G ++ ts H
{-# CATCHALL #-}
ts _       = []

-- ★ D486: the types cells hold (a closure's environment): their copy and free trampolines are live
cs : Got → List LTy
cs (c! T)  = T ∷ []
cs (G ⊹ H) = cs G ++ cs H
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
cs⊆ts (G ⊹ H) m = [ (λ p → ∈-++⁺ˡ (cs⊆ts G p)) , (λ p → ∈-++⁺ʳ (ts G) (cs⊆ts H p)) ]′ (∈-++⁻ (cs G) m)

ns : Got → List NS
ns (n! n)  = n ∷ []
ns (G ⊹ H) = ns G ++ ns H
{-# CATCHALL #-}
ns _       = []

os : Got → List DS
os (o! d)  = d ∷ []
os (G ⊹ H) = os G ++ os H
{-# CATCHALL #-}
os _       = []

ps : Got → List Sig
ps (p! s)  = s ∷ []
ps (G ⊹ H) = ps G ++ ps H
{-# CATCHALL #-}
ps _       = []

-- a term's: what its code calls by name, the types it copies or frees, the
-- ν's it builds, the tables it observes at; a closure's body with it
tmGot : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Got
tmGot ds (f ∘l g)            = tmGot ds f ⊹ tmGot ds g
tmGot ds (f ⊗l g)            = tmGot ds f ⊹ tmGot ds g
tmGot ds (lcase f g)         = tmGot ds f ⊹ tmGot ds g
tmGot ds (lcata F alg)       = k! (_ , kfold ds F alg) ⊹ tmGot ds alg
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
tmGot ds (dup {A = A})       = t! A
tmGot ds (drop {A = A})      = t! A
tmGot ds (llam {X = X} b γ)  = k! (_ , kbody1 ds b γ) ⊹ c! X ⊹ tmGot ds b
tmGot ds (llamω {X = X} b γ) = k! (_ , kbodyω ds b γ) ⊹ c! X ⊹ tmGot ds b ⊹ k! (_ , kbody1 ds (ownBg b) (ownBg-gd b γ))
-- (D480: a many-use closure also names its owned body, its owned entry's)
tmGot ds (llamωᶜ {X = X} b₀ γ) = k! (_ , kbodyω ds (cin b₀) (cin-gd b₀ γ)) ⊹ c! X ⊹ tmGot ds b₀ ⊹ k! (_ , kbody1 ds b₀ γ)
tmGot ds (lunf {F = F} {S})  = n! (F , S) ⊹ o! (_ , ε)
tmGot ds (lout {F = F})      = o! (_ , ε)
tmGot ds (lop s)             = p! s
{-# CATCHALL #-}
tmGot ds _                   = ∅

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
closeD : List AKey → (D : List LTy) → List NS → List DS → List Sig → (Cd : List LTy)
       → (R C : List LTy) → dd (R ++ C) ≡ D → dd C ≡ Cd → Univ
closeD K D N O P Cd R C eD eC =
  univ′ K D N O P Cd (λ {T} m → find T D (subst (λ Z → T ∈ Z) eD (dd⁺ (∈-++⁺ʳ R (dd⁻ C (subst (λ Z → T ∈ Z) (sym eC) m))))))

close : Got → Univ
close g = closeD (ks g) (dd ((cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) ++ (cs g ++ map cty (ns g))))
                 (ns g) ((_ , ε) ∷ os g) (ps g) (dd (cs g ++ map cty (ns g)))
                 (cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) (cs g ++ map cty (ns g)) refl refl

allK : Univ → List AKey
allK U = keys U ++ map kc (tys U) ++ map kf (tys U) ++ obsK (obs U) (nus U)

-- a program's: its table's and its main term's
univ : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Univ
univ ds f = close (defsGot ds ⊹ tmGot ds f)

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

  -- a collection inside the universe
  record _⊑U (G : Got) : Set where
    constructor sub
    field
      gk : ks G ⊆ keys U
      gt : ts G ⊆ tys U
      gn : ns G ⊆ nus U
      go : os G ⊆ obs U
      gp : ps G ⊆ ops U
      gc : cs G ⊆ cts U
  open _⊑U

  ⊹ˡ : ∀ {G H} → (G ⊹ H) ⊑U → G ⊑U
  ⊹ˡ (sub a b c d p e) = sub (λ m → a (∈-++⁺ˡ m)) (λ m → b (∈-++⁺ˡ m)) (λ m → c (∈-++⁺ˡ m)) (λ m → d (∈-++⁺ˡ m)) (λ m → p (∈-++⁺ˡ m))
                           (λ m → e (∈-++⁺ˡ m))

  ⊹ʳ : ∀ {G H} → (G ⊹ H) ⊑U → H ⊑U
  ⊹ʳ {G} (sub a b c d p e) =
    sub (λ m → a (∈-++⁺ʳ (ks G) m)) (λ m → b (∈-++⁺ʳ (ts G) m)) (λ m → c (∈-++⁺ʳ (ns G) m)) (λ m → d (∈-++⁺ʳ (os G) m))
        (λ m → p (∈-++⁺ʳ (ps G) m)) (λ m → e (∈-++⁺ʳ (cs G) m))

  ⊹-join : ∀ {G H} → G ⊑U → H ⊑U → (G ⊹ H) ⊑U
  ⊹-join {G} (sub a b c d p e) (sub a′ b′ c′ d′ p′ e′) =
    sub (λ m → [ a , a′ ] (∈-++⁻ (ks G) m)) (λ m → [ b , b′ ] (∈-++⁻ (ts G) m))
        (λ m → [ c , c′ ] (∈-++⁻ (ns G) m)) (λ m → [ d , d′ ] (∈-++⁻ (os G) m)) (λ m → [ p , p′ ] (∈-++⁻ (ps G) m))
        (λ m → [ e , e′ ] (∈-++⁻ (cs G) m))
    where
      [_,_] : ∀ {X Y Z : Set} → (X → Z) → (Y → Z) → X ⊎ Y → Z
      [ f , g ] (inj₁ x) = f x
      [ f , g ] (inj₂ y) = g y

  ∅⊑ : ∅ ⊑U
  ∅⊑ = sub (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

  -- a cell type is a copied and freed type
  ct⊑ : ∀ {X} → c! X ⊑U → t! X ⊑U
  ct⊑ g = sub (λ ()) (λ { (here refl) → cts⊆ U (gc g (here refl)) ; (there ()) }) (λ ()) (λ ()) (λ ()) (λ ())

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
  PrimIn ds (llamω {X = X} b γ) = (_ , kbodyω ds b γ) ∈ allK U × X ∈ cts U × (_ , kbody1 ds (ownBg b) (ownBg-gd b γ)) ∈ allK U
  PrimIn ds (llamωᶜ {X = X} b₀ γ) = (_ , kbodyω ds (cin b₀) (cin-gd b₀ γ)) ∈ allK U × X ∈ cts U × (_ , kbody1 ds b₀ γ) ∈ allK U
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
  comp-in ds (llamω b γ) g ck    = (inK (gk g (here refl)) , gc g (∈-++⁺ʳ [] (here refl)) , inK (gk (⊹ʳ (⊹ʳ (⊹ʳ g))) (here refl))) , ck
  comp-in ds (llamωᶜ b₀ γ) g ck  = (inK (gk g (here refl)) , gc g (∈-++⁺ʳ [] (here refl)) , inK (gk (⊹ʳ (⊹ʳ (⊹ʳ g))) (here refl))) , ck
  comp-in ds lev g ck            = tt , ck
  comp-in ds bev g ck            = tt , ck
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

  free-in : ∀ T → comps T ⊆ tys U → BIn (kf T)
  free-in One          h = tt
  free-in Zero         h = tt , tt
  free-in (A ⊗t B)     h = tt , inF (h (here refl)) , tt , inF (h (there (here refl))) , tt , tt , tt
  free-in (A ⊕t B)     h = (inF (h (here refl)) , tt) , (inF (h (there (here refl))) , tt)
  free-in (Bt b)       h = tt , tt
  free-in (μt F)       h = tt , inF (h (here refl)) , tt
  free-in (Ct l X)     h = tt , inF (h (here refl)) , tt
  free-in (Fn k g A B) h = tt , tt
  free-in (Nu F)       h = tt , tt

  -- an observation names a copy and a free of the coalgebra, and the ν's it builds
  strL-got : ∀ {Γ} (d : Defs Γ) F G S → Coalg F S ∈ tys U → tmGot d (strL F G S) ⊑U
  strL-got d F Idf      S c = ⊹-join (⊹-join (sub (λ ()) (one c) (λ ()) (λ ()) (λ ()) (λ ())) ∅⊑) ∅⊑
  strL-got d F Kone     S c = ∅⊑
  strL-got d F Kzero    S c = ∅⊑
  strL-got d F (Kb b)   S c = ∅⊑
  strL-got d F (Kμ G)   S c = ∅⊑
  strL-got d F (G ⊕f H) S c = ⊹-join (⊹-join ∅⊑ (strL-got d F G S c)) (⊹-join ∅⊑ (strL-got d F H S c))
  strL-got d F (G ⊗f H) S c = ⊹-join (strL-got d F G S c) (strL-got d F H S c)

  mapNu-got : ∀ {Γ} (d : Defs Γ) F G S → (F , S) ∈ nus U → (_ , ε) ∈ obs U → tmGot d (mapNu F G S) ⊑U
  mapNu-got d F Idf      S n o = sub (λ ()) (λ ()) (one n) (one o) (λ ()) (λ ())
  mapNu-got d F Kone     S n o = ∅⊑
  mapNu-got d F Kzero    S n o = ∅⊑
  mapNu-got d F (Kb b)   S n o = ∅⊑
  mapNu-got d F (Kμ G)   S n o = ∅⊑
  mapNu-got d F (G ⊕f H) S n o = ⊹-join (⊹-join ∅⊑ (mapNu-got d F G S n o)) (⊹-join ∅⊑ (mapNu-got d F H S n o))
  mapNu-got d F (G ⊗f H) S n o = ⊹-join (mapNu-got d F G S n o) (mapNu-got d F H S n o)

  obs-in : ∀ {Γ} (d : Defs Γ) F S → (F , S) ∈ nus U → Coalg F S ∈ tys U → (_ , ε) ∈ obs U → BIn (_ , kobs d F S)
  obs-in d F S n c o =
    tt , comp-in d (obsT F S)
           (⊹-join (mapNu-got d F F S n o)
             (⊹-join ∅⊑ (⊹-join (⊹-join (sub (λ ()) (one c) (λ ()) (λ ()) (λ ()) (λ ())) ∅⊑)
                                 (⊹-join (strL-got d F F S c) ∅⊑))))
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

  -- ★ every key a term names has its block inside
  tm-good : ∀ {Γ} {ds : Defs Γ} {E A B} (t : Tm Γ E A B) → defsGot ds ⊑U → tmGot ds t ⊑U
          → ∀ {κ} → κ ∈ ks (tmGot ds t) → BIn κ
  tm-good {ds = ds} (f ∘l h) d g m =
    [ (λ p → tm-good f d (⊹ˡ g) p) , (λ p → tm-good h d (⊹ʳ g) p) ]′ (∈-++⁻ (ks (tmGot ds f)) m)
  tm-good {ds = ds} (f ⊗l h) d g m =
    [ (λ p → tm-good f d (⊹ˡ g) p) , (λ p → tm-good h d (⊹ʳ g) p) ]′ (∈-++⁻ (ks (tmGot ds f)) m)
  tm-good {ds = ds} (lcase f h) d g m =
    [ (λ p → tm-good f d (⊹ˡ g) p) , (λ p → tm-good h d (⊹ʳ g) p) ]′ (∈-++⁻ (ks (tmGot ds f)) m)
  tm-good {ds = ds} (bcaseE f h) d g m =
    [ (λ p → tm-good f d (⊹ˡ g) p) , (λ p → tm-good h d (⊹ʳ g) p) ]′ (∈-++⁻ (ks (tmGot ds f)) m)
  tm-good (lcata F alg) d g (here refl) = tt , travI-in F (inK (gk g (here refl))) (comp-in _ alg (⊹ʳ g) tt)
  tm-good (lcata F alg) d g (there m)   = tm-good alg d (⊹ʳ g) m
  tm-good (liter f φ) d g m = tm-good f d g m
  tm-good (lend b) d g m    = tm-good b d g m
  tm-good (blift f) d g m   = tm-good f d g m
  tm-good (bfst f) d g m    = tm-good f d g m
  tm-good (bsnd f) d g m    = tm-good f d g m
  tm-good (bout f) d g m    = tm-good f d g m
  tm-good (lapp p) d g (here refl) = key1-in d p
  tm-good (lapp p) d g (there ())
  tm-good (bapp p) d g (here refl) = keyω-in d p
  tm-good (bapp p) d g (there ())
  tm-good {ds = ds} (llam b γ) d g (here refl)  = body1-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))
  tm-good (llam b γ) d g (there m)    = tm-good b d (⊹ʳ (⊹ʳ g)) m
  tm-good {ds = ds} (llamω b γ) d g (here refl) = bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ˡ (⊹ʳ (⊹ʳ g)))
  tm-good {ds = ds} (llamω {X = X} b γ) d g (there m) =
    [ (λ p → tm-good b d (⊹ˡ (⊹ʳ (⊹ʳ g))) p) , own ]′ (∈-++⁻ (ks (tmGot ds b)) m)
    where
      own : ∀ {κ} → κ ∈ (_ , kbody1 ds (ownBg b) (ownBg-gd b γ)) ∷ [] → BIn κ
      own (here refl) = body1-in {ds = ds} {b = ownBg b} {γ = ownBg-gd b γ}
                          (⊹-join (⊹-join ∅⊑ (⊹-join (ct⊑ (⊹ˡ (⊹ʳ g))) ∅⊑)) (⊹ˡ (⊹ʳ (⊹ʳ g))))
  tm-good {ds = ds} (llamωᶜ {X = X} b₀ γ) d g (here refl) =
    bodyω-in {ds = ds} {b = cin b₀} {γ = cin-gd b₀ γ} (⊹-join (⊹ˡ (⊹ʳ (⊹ʳ g))) (⊹-join (⊹-join (ct⊑ (⊹ˡ (⊹ʳ g))) ∅⊑) ∅⊑))
  tm-good {ds = ds} (llamωᶜ {X = X} b₀ γ) d g (there m) =
    [ (λ p → tm-good b₀ d (⊹ˡ (⊹ʳ (⊹ʳ g))) p) , own ]′ (∈-++⁻ (ks (tmGot ds b₀)) m)
    where
      own : ∀ {κ} → κ ∈ (_ , kbody1 ds b₀ γ) ∷ [] → BIn κ
      own (here refl) = body1-in {ds = ds} {b = b₀} {γ = γ} (⊹ˡ (⊹ʳ (⊹ʳ g)))
  tm-good lid d g ()
  tm-good ρl d g ()
  tm-good ρl⁻ d g ()
  tm-good lul d g ()
  tm-good lul⁻ d g ()
  tm-good lassoc d g ()
  tm-good lassoc⁻ d g ()
  tm-good lswap d g ()
  tm-good dup d g ()
  tm-good drop d g ()
  tm-good linl d g ()
  tm-good ldist d g ()
  tm-good linr d g ()
  tm-good lzero d g ()
  tm-good lIn d g ()
  tm-good lOutμ d g ()
  tm-good (lclo F p) d g ()
  tm-good bcopy d g ()
  tm-good lev d g ()
  tm-good bev d g ()
  tm-good levω d g ()
  tm-good lunf d g ()
  tm-good lout d g ()
  tm-good (lconst v) d g ()
  tm-good (lop s) d g ()

  defs-good : ∀ {Γ} {ds : Defs Γ} → defsGot ds ⊑U → ∀ {κ} → κ ∈ ks (defsGot ds) → BIn κ
  defs-good {ds = ε} g ()
  defs-good {ds = ds ▸ b1 b γ} g m =
    [ (λ p → defs-good (⊹ˡ g) p)
    , (λ q → [ (λ e → subst BIn (sym e) (body1-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))))
             , (λ p → tm-good b (⊹ˡ g) (⊹ʳ (⊹ʳ g)) p) ]′ (toSum q))
    ]′ (∈-++⁻ (ks (defsGot ds)) m)
  defs-good {ds = ds ▸ bω b γ} g m =
    [ (λ p → defs-good (⊹ˡ g) p)
    , (λ q → [ (λ e → subst BIn (sym e) (bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))))
             , (λ p → tm-good b (⊹ˡ g) (⊹ʳ (⊹ʳ g)) p) ]′ (toSum q))
    ]′ (∈-++⁻ (ks (defsGot ds)) m)

  -- ★ D488: the same evidence for EVERY key at once, in one pass over the term (what the compiler
  -- runs: a block's evidence is looked up in it, not searched for from its membership proof, which
  -- rebuilt every enclosing subterm's key list per block; docs/performance-patterns.md B1, B2)
  tm-all : ∀ {Γ} {ds : Defs Γ} {E A B} (t : Tm Γ E A B) → defsGot ds ⊑U → tmGot ds t ⊑U → All BIn (ks (tmGot ds t))
  tm-all (f ∘l h) d g     = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (f ⊗l h) d g     = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (lcase f h) d g  = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (bcaseE f h) d g = ++⁺ (tm-all f d (⊹ˡ g)) (tm-all h d (⊹ʳ g))
  tm-all (lcata F alg) d g = (tt , travI-in F (inK (gk g (here refl))) (comp-in _ alg (⊹ʳ g) tt)) ∷ tm-all alg d (⊹ʳ g)
  tm-all (liter f φ) d g  = tm-all f d g
  tm-all (lend b) d g     = tm-all b d g
  tm-all (blift f) d g    = tm-all f d g
  tm-all (bfst f) d g     = tm-all f d g
  tm-all (bsnd f) d g     = tm-all f d g
  tm-all (bout f) d g     = tm-all f d g
  tm-all (lapp p) d g     = key1-in d p ∷ []
  tm-all (bapp p) d g     = keyω-in d p ∷ []
  tm-all {ds = ds} (llam b γ) d g = body1-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g)) ∷ tm-all b d (⊹ʳ (⊹ʳ g))
  tm-all {ds = ds} (llamω b γ) d g =
    bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ˡ (⊹ʳ (⊹ʳ g)))
    ∷ ++⁺ (tm-all b d (⊹ˡ (⊹ʳ (⊹ʳ g))))
          (body1-in {ds = ds} {b = ownBg b} {γ = ownBg-gd b γ}
             (⊹-join (⊹-join ∅⊑ (⊹-join (ct⊑ (⊹ˡ (⊹ʳ g))) ∅⊑)) (⊹ˡ (⊹ʳ (⊹ʳ g)))) ∷ [])
  tm-all {ds = ds} (llamωᶜ b₀ γ) d g =
    bodyω-in {ds = ds} {b = cin b₀} {γ = cin-gd b₀ γ} (⊹-join (⊹ˡ (⊹ʳ (⊹ʳ g))) (⊹-join (⊹-join (ct⊑ (⊹ˡ (⊹ʳ g))) ∅⊑) ∅⊑))
    ∷ ++⁺ (tm-all b₀ d (⊹ˡ (⊹ʳ (⊹ʳ g)))) (body1-in {ds = ds} {b = b₀} {γ = γ} (⊹ˡ (⊹ʳ (⊹ʳ g))) ∷ [])
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
  g₀⊑ = sub (λ m → mv keys m) (λ {T} m → inT (∈-++⁺ˡ (∈-++⁺ˡ (∈-cmap⁺ (ts g₀) m (here refl))))) (λ m → mv nus m)
            (λ m → mv obs (there m)) (λ m → mv ops m) (λ {T} m → find T (cts U) (mv cts (dd⁺ (∈-++⁺ˡ m))))

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
    ++⁺ (subst (λ W → All BIn (keys W)) eV (++⁺ (defs-all (⊹ˡ g₀⊑)) (tm-all f (⊹ˡ g₀⊑) (⊹ʳ g₀⊑))))
        (++⁺ (map⁺ (tabulate (λ {T} t → copy-in T (ts-closed t))))
             (++⁺ (map⁺ (tabulate (λ {T} t → free-in T (ts-closed t))))
                  (tabulate (λ r → let ((Δ , d) , o , s) = ∈-cmap⁻ (obs U) r
                                       ((F , S) , n , e) = ∈-map⁻ (λ n → _ , kobs d (proj₁ n) (proj₂ n)) s
                                   in subst BIn (sym e) (obs-in d F S n (ns-coalg n) (mv obs (here refl)))))))

  -- (opaque: a proof; sealed, two spellings of a block's evidence compare as one stuck term)
  opaque
    blocks-in : ∀ {κ} → κ ∈ allK U → BIn κ
    blocks-in = lookupA blocks-all

  -- ★ and so is the program's start
  start-in : ∀ {Es S T} {k : Codeᴵ (One ∷ Es ∣ One ∷ S) T} → CIn k → CIn (compᴵ ds f k)
  start-in ck = comp-in ds f (⊹ʳ g₀⊑) ck

-- the program's: at its own universe
module Program {Γ} (ds : Defs Γ) (f : LTm Γ One One) = ProgramW ds f (univ ds f) refl
