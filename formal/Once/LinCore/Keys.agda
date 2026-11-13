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
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.Keys
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw

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
∈-cmap⁻ {f = f} (x ∷ xs) m with ∈-++⁻ (f x) m
... | inj₁ p = x , here refl , p
... | inj₂ p with ∈-cmap⁻ xs p
...   | (z , q , r) = z , there q , r

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
closedF (G ⊕f H) F h₁ h₂ (there m) c with ∈-++⁻ (subsF G F) m
... | inj₁ p = closedF G F (λ q → h₁ (there (∈-++⁺ˡ q))) h₂ p c
... | inj₂ p = closedF H F (λ q → h₁ (there (∈-++⁺ʳ (subsF G F) q))) h₂ p c
closedF (G ⊗f H) F h₁ h₂ (there m) c with ∈-++⁻ (subsF G F) m
... | inj₁ p = closedF G F (λ q → h₁ (there (∈-++⁺ˡ q))) h₂ p c
... | inj₂ p = closedF H F (λ q → h₁ (there (∈-++⁺ʳ (subsF G F) q))) h₂ p c

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
closed (A ⊗t B) (there m) c with ∈-++⁻ (subs A) m
... | inj₁ p = there (∈-++⁺ˡ (closed A p c))
... | inj₂ p = there (∈-++⁺ʳ (subs A) (closed B p c))
closed (A ⊕t B) (there m) c with ∈-++⁻ (subs A) m
... | inj₁ p = there (∈-++⁺ˡ (closed A p c))
... | inj₂ p = there (∈-++⁺ʳ (subs A) (closed B p c))
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
  n!  : NS → Got
  o!  : DS → Got
  _⊹_ : Got → Got → Got

ks : Got → List AKey
ks (k! κ)  = κ ∷ []
ks (G ⊹ H) = ks G ++ ks H
{-# CATCHALL #-}
ks _       = []

ts : Got → List LTy
ts (t! T)  = T ∷ []
ts (G ⊹ H) = ts G ++ ts H
{-# CATCHALL #-}
ts _       = []

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
tmGot ds (llam {X = X} b γ)  = k! (_ , kbody1 ds b γ) ⊹ t! X ⊹ tmGot ds b
tmGot ds (llamω {X = X} b γ) = k! (_ , kbodyω ds b γ) ⊹ t! X ⊹ tmGot ds b
tmGot ds (lunf {F = F} {S})  = n! (F , S) ⊹ o! (_ , ε)
tmGot ds (lout {F = F})      = o! (_ , ε)
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
open Univ public

close : Got → Univ
close g = univ′ (ks g) (cmap subs (ts g) ++ cmap (λ n → subs (cty n)) (ns g)) (ns g) ((_ , ε) ∷ os g)

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
  open _⊑U public

  ⊹ˡ : ∀ {G H} → (G ⊹ H) ⊑U → G ⊑U
  ⊹ˡ (sub a b c d) = sub (λ m → a (∈-++⁺ˡ m)) (λ m → b (∈-++⁺ˡ m)) (λ m → c (∈-++⁺ˡ m)) (λ m → d (∈-++⁺ˡ m))

  ⊹ʳ : ∀ {G H} → (G ⊹ H) ⊑U → H ⊑U
  ⊹ʳ {G} (sub a b c d) =
    sub (λ m → a (∈-++⁺ʳ (ks G) m)) (λ m → b (∈-++⁺ʳ (ts G) m)) (λ m → c (∈-++⁺ʳ (ns G) m)) (λ m → d (∈-++⁺ʳ (os G) m))

  ⊹-join : ∀ {G H} → G ⊑U → H ⊑U → (G ⊹ H) ⊑U
  ⊹-join {G} (sub a b c d) (sub a′ b′ c′ d′) =
    sub (λ m → [ a , a′ ] (∈-++⁻ (ks G) m)) (λ m → [ b , b′ ] (∈-++⁻ (ts G) m))
        (λ m → [ c , c′ ] (∈-++⁻ (ns G) m)) (λ m → [ d , d′ ] (∈-++⁻ (os G) m))
    where
      [_,_] : ∀ {X Y Z : Set} → (X → Z) → (Y → Z) → X ⊎ Y → Z
      [ f , g ] (inj₁ x) = f x
      [ f , g ] (inj₂ y) = g y

  ∅⊑ : ∅ ⊑U
  ∅⊑ = sub (λ ()) (λ ()) (λ ()) (λ ())

  ----------------------------------------------------------------------
  -- 4. CODE INSIDE THE UNIVERSE: every call, every closure or ν a `prim`
  -- builds, every observation's table.
  ----------------------------------------------------------------------

  PrimIn : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Set
  PrimIn ds (llam {X = X} b γ)  = (_ , kbody1 ds b γ) ∈ allK U × X ∈ tys U
  PrimIn ds (llamω {X = X} b γ) = (_ , kbodyω ds b γ) ∈ allK U × X ∈ tys U
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
  PrimIn ds linr      = ⊤
  PrimIn ds lIn       = ⊤
  PrimIn ds lOutμ     = ⊤
  PrimIn ds (lclo F p) = ⊤
  PrimIn ds (lconst v) = ⊤
  PrimIn ds (lop s)   = ⊤
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

  -- ★ a term's code is inside when what it names is
  comp-in : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) {Es S T} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) T}
          → tmGot ds t ⊑U → CIn k → CIn (compᴵ ds t k)
  comp-in ds lid g ck            = ck
  comp-in ds (f ∘l h) g ck       = comp-in ds h (⊹ʳ g) (comp-in ds f (⊹ˡ g) ck)
  comp-in ds (f ⊗l h) g ck       = tt , comp-in ds f (⊹ˡ g) (tt , comp-in ds h (⊹ʳ g) (tt , tt , ck))
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
  comp-in ds linr g ck           = tt , ck
  comp-in ds lIn g ck            = tt , ck
  comp-in ds lOutμ g ck          = tt , ck
  comp-in ds (lclo F p) g ck     = tt , ck
  comp-in ds (lconst v) g ck     = tt , ck
  comp-in ds (lop s) g ck        = tt , ck
  comp-in ds lzero g ck          = tt , ck
  comp-in ds (llam b γ) g ck     = (inK (gk g (here refl)) , gt g (∈-++⁺ʳ [] (here refl))) , ck
  comp-in ds (llamω b γ) g ck    = (inK (gk g (here refl)) , gt g (∈-++⁺ʳ [] (here refl))) , ck
  comp-in ds lev g ck            = tt , ck
  comp-in ds bev g ck            = tt , ck
  comp-in ds lunf g ck           = (gn g (here refl) , go g (here refl)) , ck
  comp-in ds lout g ck           = go g (here refl) , ck

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
  strL-got d F Idf      S c = ⊹-join (⊹-join (sub (λ ()) (one c) (λ ()) (λ ())) ∅⊑) ∅⊑
  strL-got d F Kone     S c = ∅⊑
  strL-got d F Kzero    S c = ∅⊑
  strL-got d F (Kb b)   S c = ∅⊑
  strL-got d F (Kμ G)   S c = ∅⊑
  strL-got d F (G ⊕f H) S c = ⊹-join (⊹-join ∅⊑ (strL-got d F G S c)) (⊹-join ∅⊑ (strL-got d F H S c))
  strL-got d F (G ⊗f H) S c = ⊹-join (strL-got d F G S c) (strL-got d F H S c)

  mapNu-got : ∀ {Γ} (d : Defs Γ) F G S → (F , S) ∈ nus U → (_ , ε) ∈ obs U → tmGot d (mapNu F G S) ⊑U
  mapNu-got d F Idf      S n o = sub (λ ()) (λ ()) (one n) (one o)
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
             (⊹-join ∅⊑ (⊹-join (⊹-join (sub (λ ()) (one c) (λ ()) (λ ())) ∅⊑)
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
  tm-good {ds = ds} (f ∘l h) d g m with ∈-++⁻ (ks (tmGot ds f)) m
  ... | inj₁ p = tm-good f d (⊹ˡ g) p
  ... | inj₂ p = tm-good h d (⊹ʳ g) p
  tm-good {ds = ds} (f ⊗l h) d g m with ∈-++⁻ (ks (tmGot ds f)) m
  ... | inj₁ p = tm-good f d (⊹ˡ g) p
  ... | inj₂ p = tm-good h d (⊹ʳ g) p
  tm-good {ds = ds} (lcase f h) d g m with ∈-++⁻ (ks (tmGot ds f)) m
  ... | inj₁ p = tm-good f d (⊹ˡ g) p
  ... | inj₂ p = tm-good h d (⊹ʳ g) p
  tm-good {ds = ds} (bcaseE f h) d g m with ∈-++⁻ (ks (tmGot ds f)) m
  ... | inj₁ p = tm-good f d (⊹ˡ g) p
  ... | inj₂ p = tm-good h d (⊹ʳ g) p
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
  tm-good {ds = ds} (llamω b γ) d g (here refl) = bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))
  tm-good (llamω b γ) d g (there m)   = tm-good b d (⊹ʳ (⊹ʳ g)) m
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
  tm-good linr d g ()
  tm-good lzero d g ()
  tm-good lIn d g ()
  tm-good lOutμ d g ()
  tm-good (lclo F p) d g ()
  tm-good bcopy d g ()
  tm-good lev d g ()
  tm-good bev d g ()
  tm-good lunf d g ()
  tm-good lout d g ()
  tm-good (lconst v) d g ()
  tm-good (lop s) d g ()

  defs-good : ∀ {Γ} {ds : Defs Γ} → defsGot ds ⊑U → ∀ {κ} → κ ∈ ks (defsGot ds) → BIn κ
  defs-good {ds = ε} g ()
  defs-good {ds = ds ▸ b1 b γ} g m with ∈-++⁻ (ks (defsGot ds)) m
  ... | inj₁ p           = defs-good (⊹ˡ g) p
  ... | inj₂ (here refl) = body1-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))
  ... | inj₂ (there p)   = tm-good b (⊹ˡ g) (⊹ʳ (⊹ʳ g)) p
  defs-good {ds = ds ▸ bω b γ} g m with ∈-++⁻ (ks (defsGot ds)) m
  ... | inj₁ p           = defs-good (⊹ˡ g) p
  ... | inj₂ (here refl) = bodyω-in {ds = ds} {b = b} {γ = γ} (⊹ʳ (⊹ʳ g))
  ... | inj₂ (there p)   = tm-good b (⊹ˡ g) (⊹ʳ (⊹ʳ g)) p

------------------------------------------------------------------------
-- 6. ★ A PROGRAM'S UNIVERSE IS CLOSED: its blocks and its start are inside.
------------------------------------------------------------------------

module Program {Γ} (ds : Defs Γ) (f : LTm Γ One One) where

  g₀ : Got
  g₀ = defsGot ds ⊹ tmGot ds f

  U : Univ
  U = univ ds f

  open In U public

  g₀⊑ : g₀ ⊑U
  g₀⊑ = sub (λ m → m) (λ {T} m → ∈-++⁺ˡ (∈-cmap⁺ (ts g₀) m (here refl))) (λ m → m) there

  -- the types are closed under a copy's or a free's parts
  ts-closed : ∀ {T} → T ∈ tys U → comps T ⊆ tys U
  ts-closed {T} m c with ∈-++⁻ (cmap subs (ts g₀)) m
  ... | inj₁ p with ∈-cmap⁻ (ts g₀) p
  ...   | (R , r , q) = ∈-++⁺ˡ (∈-cmap⁺ (ts g₀) r (closed R q c))
  ts-closed {T} m c | inj₂ p with ∈-cmap⁻ (ns g₀) p
  ...   | (n , r , q) = ∈-++⁺ʳ (cmap subs (ts g₀)) (∈-cmap⁺ (ns g₀) r (closed (cty n) q c))

  -- a ν's coalgebra type is among them
  ns-coalg : ∀ {F S} → (F , S) ∈ nus U → Coalg F S ∈ tys U
  ns-coalg n = ∈-++⁺ʳ (cmap subs (ts g₀)) (∈-cmap⁺ (ns g₀) n (there (here refl)))

  -- ★ EVERY BLOCK OF THE UNIVERSE IS INSIDE IT
  blocks-in : ∀ {κ} → κ ∈ allK U → BIn κ
  blocks-in m with ∈-++⁻ (keys U) m
  ... | inj₁ p with ∈-++⁻ (ks (defsGot ds)) p
  ...   | inj₁ q = defs-good (⊹ˡ g₀⊑) q
  ...   | inj₂ q = tm-good f (⊹ˡ g₀⊑) (⊹ʳ g₀⊑) q
  blocks-in m | inj₂ p with ∈-++⁻ (map kc (tys U)) p
  ... | inj₁ q with ∈-map⁻ kc q
  ...   | (T , t , refl) = copy-in T (ts-closed t)
  blocks-in m | inj₂ p | inj₂ q with ∈-++⁻ (map kf (tys U)) q
  ... | inj₁ r with ∈-map⁻ kf r
  ...   | (T , t , refl) = free-in T (ts-closed t)
  blocks-in m | inj₂ p | inj₂ q | inj₂ r with ∈-cmap⁻ (obs U) r
  ... | ((Δ , d) , o , s) with ∈-map⁻ (λ n → _ , kobs d (proj₁ n) (proj₂ n)) s
  ...   | ((F , S) , n , refl) = obs-in d F S n (ns-coalg n) (here refl)

  -- ★ and so is the program's start
  start-in : ∀ {Es S T} {k : Codeᴵ (One ∷ Es ∣ One ∷ S) T} → CIn k → CIn (compᴵ ds f k)
  start-in ck = comp-in ds f (⊹ʳ g₀⊑) ck
