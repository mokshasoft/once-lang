-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Principal — the principal-type ORACLE (D072).
--
-- Computes the principal type of a sig-less definition body by
-- first-order unification over `PolyType`, with metavariables spelled
-- `PTVar "?n"` (the parser cannot produce a `?`-identifier, so the
-- namespace is reserved) and generalization only at the definition
-- boundary.
--
-- TRUST STATUS: UNTRUSTED BY DESIGN. Nothing in the verified pipeline
-- depends on any property of this module — every answer is re-checked
-- by the verified elaborator (`checkElab`) before it is used
-- (check-after-infer, D072). A wrong answer here is a rejected
-- program, never an unsound one. Consequently this module carries NO
-- proofs (string-literal patterns are fine here — no proof ever
-- case-splits this code); its completeness ("if any type exists, the
-- principal one is found") is the open D072 obligation.
--
-- Canon-invariance by construction: `RVar x` and `RResolved cn`
-- dispatch through the same name-keyed lookup (`lookupName`), keyed by
-- `showCanonical`.
--
-- Totality: unification and zonking are fuel-bounded (fuel exhaustion
-- = inference failure = "add a signature"), the syntax traversal is
-- structural.
------------------------------------------------------------------------

module Once.TypeCheck.Principal where

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
import Relation.Nullary

open import Once.Type
open import Once.CanonicalName using (CanonicalName; canonical; showCanonical; gen; generatorNS; _≟ᶜ_)
open import Once.TypeCheck.Raw as Raw
  using (RawExpr; BinOp; UnaryOp; isComparisonOp)
open import Once.TypeCheck.Classify
  using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPoly; emptyCtx)

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

isYes : ∀ {a} {P : Set a} → Relation.Nullary.Dec P → Bool
isYes (yes _) = true
isYes (no _)  = false

eqQuantity : Quantity → Quantity → Bool
eqQuantity Zero Zero = true
eqQuantity One  One  = true
eqQuantity Many Many = true
eqQuantity _    _    = false

map2P : (PolyType → PolyType → PolyType)
      → Maybe PolyType → Maybe PolyType → Maybe PolyType
map2P f (just a) (just b) = just (f a b)
map2P _ _ _ = nothing

map2F : (PolyFunctor → PolyFunctor → PolyFunctor)
      → Maybe PolyFunctor → Maybe PolyFunctor → Maybe PolyFunctor
map2F f (just a) (just b) = just (f a b)
map2F _ _ _ = nothing

------------------------------------------------------------------------
-- Metavariables and substitutions
------------------------------------------------------------------------

-- | Fresh metavariable names live in the reserved `?` namespace.
mv : ℕ → String
mv n = "?" ++ showℕ n

PSubst : Set
PSubst = List (String × PolyType)

lookupP : String → PSubst → Maybe PolyType
lookupP _ [] = nothing
lookupP x ((y , t) ∷ rest) with x ≟ y
... | yes _ = just t
... | no _  = lookupP x rest

-- | Resolve top-level metavariable chains (fuel-bounded).
walk : ℕ → PSubst → PolyType → PolyType
walk zero _ t = t
walk (suc n) s (PTVar x) with lookupP x s
... | just t  = walk n s t
... | nothing = PTVar x
walk (suc _) _ t = t

-- | Full deep substitution (fuel spent following solutions AND on
-- structure — one counter keeps the termination argument trivial).
mutual
  zonk : ℕ → PSubst → PolyType → PolyType
  zonk zero _ t = t
  zonk (suc n) s (PTVar x) with lookupP x s
  ... | just t  = zonk n s t
  ... | nothing = PTVar x
  zonk (suc n) s (a P* b)      = zonk n s a P* zonk n s b
  zonk (suc n) s (a P+ b)      = zonk n s a P+ zonk n s b
  zonk (suc n) s (a P⇒[ q ] b) = zonk n s a P⇒[ q ] zonk n s b
  zonk (suc n) s (PEff a b)    = PEff (zonk n s a) (zonk n s b)
  zonk (suc n) s (Pμ-type F)   = Pμ-type (zonkF n s F)
  zonk (suc n) s (Pν-type F)   = Pν-type (zonkF n s F)
  zonk (suc _) _ t = t

  zonkF : ℕ → PSubst → PolyFunctor → PolyFunctor
  zonkF zero _ F = F
  zonkF (suc n) s (PK A)   = PK (zonk n s A)
  zonkF (suc _) _ PId      = PId
  zonkF (suc n) s (F P⊕ G) = zonkF n s F P⊕ zonkF n s G
  zonkF (suc n) s (F P⊗ G) = zonkF n s F P⊗ zonkF n s G

-- | Occurs check (call on zonked terms).
mutual
  occurs : String → PolyType → Bool
  occurs x (PTVar y) with x ≟ y
  ... | yes _ = true
  ... | no _  = false
  occurs x (a P* b)      = occurs x a ∨ occurs x b
  occurs x (a P+ b)      = occurs x a ∨ occurs x b
  occurs x (a P⇒[ _ ] b) = occurs x a ∨ occurs x b
  occurs x (PEff a b)    = occurs x a ∨ occurs x b
  occurs x (Pμ-type F)   = occursF x F
  occurs x (Pν-type F)   = occursF x F
  occurs _ _ = false

  occursF : String → PolyFunctor → Bool
  occursF x (PK A)   = occurs x A
  occursF _ PId      = false
  occursF x (F P⊕ G) = occursF x F ∨ occursF x G
  occursF x (F P⊗ G) = occursF x F ∨ occursF x G

-- | Bind a metavariable to a (zonked) solution, occurs-checked.
bindVar : ℕ → String → PolyType → PSubst → Maybe PSubst
bindVar fuel x t s = go (zonk fuel s t)
  where
  go : PolyType → Maybe PSubst
  go (PTVar y) with x ≟ y
  ... | yes _ = just s
  ... | no _  = just ((x , PTVar y) ∷ s)
  go t' = if occurs x t' then nothing else just ((x , t') ∷ s)

------------------------------------------------------------------------
-- Unification (fuel-bounded; every PTVar in play is a metavariable —
-- schemas are freshened before entering the solver, so no rigid
-- variables exist in v1)
------------------------------------------------------------------------

mutual
  unify : ℕ → PSubst → PolyType → PolyType → Maybe PSubst
  unify zero _ _ _ = nothing
  unify (suc n) s a b = unify' n s (walk n s a) (walk n s b)

  unify' : ℕ → PSubst → PolyType → PolyType → Maybe PSubst
  unify' n s (PTVar x) t = bindVar n x t s
  unify' n s t (PTVar x) = bindVar n x t s
  unify' n s PUnit PUnit = just s
  unify' n s PVoid PVoid = just s
  unify' n s PInt PInt = just s
  unify' n s PFloat PFloat = just s
  unify' n s PStr PStr = just s
  unify' n s PBuffer PBuffer = just s
  unify' n s (a P* b) (a' P* b') = unify2 n s a a' b b'
  unify' n s (a P+ b) (a' P+ b') = unify2 n s a a' b b'
  unify' n s (a P⇒[ q ] b) (a' P⇒[ q' ] b') =
    if eqQuantity q q' then unify2 n s a a' b b' else nothing
  unify' n s (PEff a b) (PEff a' b') = unify2 n s a a' b b'
  unify' n s (Pμ-type F) (Pμ-type G) = unifyF n s F G
  unify' n s (Pν-type F) (Pν-type G) = unifyF n s F G
  unify' _ _ _ _ = nothing

  unify2 : ℕ → PSubst → PolyType → PolyType → PolyType → PolyType → Maybe PSubst
  unify2 n s a a' b b' with unify n s a a'
  ... | nothing = nothing
  ... | just s' = unify n s' b b'

  unifyF : ℕ → PSubst → PolyFunctor → PolyFunctor → Maybe PSubst
  unifyF zero _ _ _ = nothing
  unifyF (suc n) s (PK A) (PK B)     = unify n s A B
  unifyF (suc _) s PId PId           = just s
  unifyF (suc n) s (F P⊕ G) (F' P⊕ G') with unifyF n s F F'
  ... | nothing = nothing
  ... | just s' = unifyF n s' G G'
  unifyF (suc n) s (F P⊗ G) (F' P⊗ G') with unifyF n s F F'
  ... | nothing = nothing
  ... | just s' = unifyF n s' G G'
  unifyF (suc _) _ _ _ = nothing

------------------------------------------------------------------------
-- Embedding ground Types into PolyType (partial: arrows with a
-- non-`Many` eff kind have no PolyType image — oracle failure there
-- means "add a signature", never unsoundness)
------------------------------------------------------------------------

mutual
  typeToPoly : Type → Maybe PolyType
  typeToPoly Unit = just PUnit
  typeToPoly Void = just PVoid
  typeToPoly Int = just PInt
  typeToPoly Float = just PFloat
  typeToPoly Str = just PStr
  typeToPoly Buffer = just PBuffer
  typeToPoly (a * b) = map2P _P*_ (typeToPoly a) (typeToPoly b)
  typeToPoly (a + b) = map2P _P+_ (typeToPoly a) (typeToPoly b)
  typeToPoly (a ⇒[ mk-kind q pure ] b) =
    map2P (λ x y → x P⇒[ q ] y) (typeToPoly a) (typeToPoly b)
  typeToPoly (a ⇒[ mk-kind Many eff ] b) =
    map2P PEff (typeToPoly a) (typeToPoly b)
  typeToPoly (a ⇒[ mk-kind _ eff ] b) = nothing
  typeToPoly (μ-type F) with functorToPoly F
  ... | just G  = just (Pμ-type G)
  ... | nothing = nothing
  typeToPoly (ν-type F) with functorToPoly F
  ... | just G  = just (Pν-type G)
  ... | nothing = nothing

  functorToPoly : Functor → Maybe PolyFunctor
  functorToPoly (K A) with typeToPoly A
  ... | just B  = just (PK B)
  ... | nothing = nothing
  functorToPoly Id = just PId
  functorToPoly (F ⊕ G) = map2F _P⊕_ (functorToPoly F) (functorToPoly G)
  functorToPoly (F ⊗ G) = map2F _P⊗_ (functorToPoly F) (functorToPoly G)

------------------------------------------------------------------------
-- Schemas: builtins and freshening
------------------------------------------------------------------------

-- | Schemas of the polymorphic builtins, minted with fresh
-- metavariables starting at counter `n`. `compose` is NOT here — it is
-- grade-polymorphic (pure/eff), which the schema grammar cannot
-- express; the traversal special-cases it. `cata`/`In`/`ana` need
-- functor metavariables — out of scope for v1 (signature required).
builtinSchema : String → ℕ → Maybe (PolyType × ℕ)
builtinSchema "id" n =
  just (PTVar (mv n) P⇒[ Many ] PTVar (mv n) , suc n)
builtinSchema "fst" n =
  just ((PTVar (mv n) P* PTVar (mv (suc n))) P⇒[ Many ] PTVar (mv n) ,
        suc (suc n))
builtinSchema "snd" n =
  just ((PTVar (mv n) P* PTVar (mv (suc n))) P⇒[ Many ] PTVar (mv (suc n)) ,
        suc (suc n))
builtinSchema "inl" n =
  just (PTVar (mv n) P⇒[ Many ] (PTVar (mv n) P+ PTVar (mv (suc n))) ,
        suc (suc n))
builtinSchema "inr" n =
  just (PTVar (mv (suc n)) P⇒[ Many ] (PTVar (mv n) P+ PTVar (mv (suc n))) ,
        suc (suc n))
builtinSchema "terminal" n =
  just (PTVar (mv n) P⇒[ Many ] PUnit , suc n)
builtinSchema "initial" n =
  just (PVoid P⇒[ Many ] PTVar (mv n) , suc n)
builtinSchema "unit" n = just (PUnit , n)
builtinSchema "apply" n =
  just (((PTVar (mv n) P⇒[ Many ] PTVar (mv (suc n))) P* PTVar (mv n))
          P⇒[ Many ] PTVar (mv (suc n)) ,
        suc (suc n))
builtinSchema "curry" n =
  just (((PTVar (mv n) P* PTVar (mv (suc n))) P⇒[ Many ] PTVar (mv (suc (suc n))))
          P⇒[ Many ]
        (PTVar (mv n) P⇒[ Many ] (PTVar (mv (suc n)) P⇒[ Many ] PTVar (mv (suc (suc n))))) ,
        suc (suc (suc n)))
builtinSchema "pair" n =
  just ((PTVar (mv (suc (suc n))) P⇒[ Many ] PTVar (mv n))
          P⇒[ Many ]
        ((PTVar (mv (suc (suc n))) P⇒[ Many ] PTVar (mv (suc n)))
          P⇒[ Many ]
         (PTVar (mv (suc (suc n))) P⇒[ Many ] (PTVar (mv n) P* PTVar (mv (suc n))))) ,
        suc (suc (suc n)))
builtinSchema "case" n =
  just ((PTVar (mv n) P⇒[ Many ] PTVar (mv (suc (suc n))))
          P⇒[ Many ]
        ((PTVar (mv (suc n)) P⇒[ Many ] PTVar (mv (suc (suc n))))
          P⇒[ Many ]
         ((PTVar (mv n) P+ PTVar (mv (suc n))) P⇒[ Many ] PTVar (mv (suc (suc n))))) ,
        suc (suc (suc n)))
builtinSchema _ _ = nothing

lookupRen : String → List (String × String) → Maybe String
lookupRen _ [] = nothing
lookupRen x ((y , z) ∷ rest) with x ≟ y
... | yes _ = just z
... | no _  = lookupRen x rest

-- | Rename a schema's variables to fresh metavariables (instantiation
-- of a user poly def at a use site). Accumulates old→new pairs so a
-- variable is renamed consistently.
mutual
  freshen : PolyType → ℕ → List (String × String)
          → PolyType × ℕ × List (String × String)
  freshen (PTVar x) n acc with lookupRen x acc
  ... | just y  = PTVar y , n , acc
  ... | nothing = PTVar (mv n) , suc n , (x , mv n) ∷ acc
  freshen (a P* b) n acc =
    let (a' , n₁ , acc₁) = freshen a n acc
        (b' , n₂ , acc₂) = freshen b n₁ acc₁
    in a' P* b' , n₂ , acc₂
  freshen (a P+ b) n acc =
    let (a' , n₁ , acc₁) = freshen a n acc
        (b' , n₂ , acc₂) = freshen b n₁ acc₁
    in a' P+ b' , n₂ , acc₂
  freshen (a P⇒[ q ] b) n acc =
    let (a' , n₁ , acc₁) = freshen a n acc
        (b' , n₂ , acc₂) = freshen b n₁ acc₁
    in a' P⇒[ q ] b' , n₂ , acc₂
  freshen (PEff a b) n acc =
    let (a' , n₁ , acc₁) = freshen a n acc
        (b' , n₂ , acc₂) = freshen b n₁ acc₁
    in PEff a' b' , n₂ , acc₂
  freshen (Pμ-type F) n acc =
    let (F' , n₁ , acc₁) = freshenF F n acc in Pμ-type F' , n₁ , acc₁
  freshen (Pν-type F) n acc =
    let (F' , n₁ , acc₁) = freshenF F n acc in Pν-type F' , n₁ , acc₁
  freshen t n acc = t , n , acc

  freshenF : PolyFunctor → ℕ → List (String × String)
           → PolyFunctor × ℕ × List (String × String)
  freshenF (PK A) n acc =
    let (A' , n₁ , acc₁) = freshen A n acc in PK A' , n₁ , acc₁
  freshenF PId n acc = PId , n , acc
  freshenF (F P⊕ G) n acc =
    let (F' , n₁ , acc₁) = freshenF F n acc
        (G' , n₂ , acc₂) = freshenF G n₁ acc₁
    in F' P⊕ G' , n₂ , acc₂
  freshenF (F P⊗ G) n acc =
    let (F' , n₁ , acc₁) = freshenF F n acc
        (G' , n₂ , acc₂) = freshenF G n₁ acc₁
    in F' P⊗ G' , n₂ , acc₂

------------------------------------------------------------------------
-- The W-style traversal
------------------------------------------------------------------------

-- | Local environment for lambda/let/destruct binders (their types may
-- contain metavariables, so they cannot live in `NamedCtx`).
Env : Set
Env = List (String × PolyType)

lookupEnv : String → Env → Maybe PolyType
lookupEnv _ [] = nothing
lookupEnv x ((y , t) ∷ rest) with x ≟ y
... | yes _ = just t
... | no _  = lookupEnv x rest

-- | Traversal result: inferred type, fresh counter, substitution.
Result : Set
Result = Maybe (PolyType × ℕ × PSubst)

fuelD : ℕ
fuelD = 500

infixl 1 _>>=R_
_>>=R_ : Result → (PolyType × ℕ × PSubst → Result) → Result
just x  >>=R f = f x
nothing >>=R _ = nothing

retTy : PolyType → ℕ → Maybe PSubst → Result
retTy t n (just s) = just (t , n , s)
retTy _ _ nothing  = nothing

-- | The oracle's context view: the import table plus poly SCHEMAS
-- only. `pInfer` cannot depend on poly BODIES *by type* — which is what
-- makes canon-invariance over `canonPolysCtx` (bodies-only) a plain
-- congruence (CanonPrincipal).
SchemaCtx : Set
SchemaCtx = List (String × PolyType)

projSchemas : PolyCtx → SchemaCtx
projSchemas [] = []
projSchemas ((nm , sc , _) ∷ rest) = (nm , sc) ∷ projSchemas rest

lookupSchema : SchemaCtx → String → Maybe PolyType
lookupSchema [] _ = nothing
lookupSchema ((y , sc) ∷ rest) x with x ≟ y
... | yes _ = just sc
... | no _  = lookupSchema rest x

-- | D136: a GENERATOR's schema is keyed on its bare name (`builtinSchema "id"`),
-- so the canonical form has to be peeled before lookup — otherwise the oracle
-- asks for `"Generators.id"`, finds nothing, and a sig-less `f = id` stops
-- inferring. Every other canonical name keys on the dotted path, as before.
canonKey : CanonicalName → String
canonKey (canonical (ns ∷ g ∷ [])) with ns ≟ generatorNS
... | yes _ = g
... | no  _ = showCanonical (canonical (ns ∷ g ∷ []))
canonKey cn = showCanonical cn

-- | Name-keyed leaf lookup, shared by `RVar` and `RResolved` so the two
-- coincide (canon-invariance by construction). Order matches the
-- kernel's dispatch: builtin, then user poly def, then import.
lookupName : Imports → SchemaCtx → String → ℕ → Maybe (PolyType × ℕ)
lookupName imps sch name n with builtinSchema name n
... | just r = just r
... | nothing with lookupSchema sch name
...   | just schema =
        let (t , n' , _) = freshen schema n [] in just (t , n')
...   | nothing with lookupImport imps name
...     | nothing = nothing
...     | just T with typeToPoly T
...       | just t  = just (t , n)
...       | nothing = nothing

liftName : Maybe (PolyType × ℕ) → PSubst → Result
liftName (just (t , n)) s = just (t , n , s)
liftName nothing _ = nothing

-- | Decompose an arrow-ish type, binding a metavariable head to a
-- fresh pure arrow. Returns (domain, codomain, isEff, subst, counter).
arrowParts : PSubst → PolyType → ℕ → Maybe (PolyType × PolyType × Bool × PSubst × ℕ)
arrowParts s t n = go (walk fuelD s t)
  where
  go : PolyType → Maybe (PolyType × PolyType × Bool × PSubst × ℕ)
  go (a P⇒[ _ ] b) = just (a , b , false , s , n)
  go (PEff a b)    = just (a , b , true , s , n)
  go (PTVar x) with bindVar fuelD x (PTVar (mv n) P⇒[ Many ] PTVar (mv (suc n))) s
  ... | just s' = just (PTVar (mv n) , PTVar (mv (suc n)) , false , s' , suc (suc n))
  ... | nothing = nothing
  go _ = nothing

-- | Finish a general application `f x` once both types are inferred.
-- Mirrors the kernel: pure arrow applies to its codomain; an eff arrow
-- application yields the thunk `Eff Unit B` (t-effApp).
appFinish : PolyType → PolyType → ℕ → PSubst → Result
appFinish tf tx n s with arrowParts s tf n
... | nothing = nothing
... | just (a , b , isEff , s₁ , n₁) with unify fuelD s₁ a tx
...   | nothing = nothing
...   | just s₂ = just ((if isEff then PEff PUnit b else b) , n₁ , s₂)

-- | Finish `compose f g` (grade-polymorphic: eff iff either arm eff).
composeFinish : PolyType → PolyType → ℕ → PSubst → Result
composeFinish tf tg n s with arrowParts s tf n
... | nothing = nothing
... | just (bf , cf , ef , s₁ , n₁) with arrowParts s₁ tg n₁
...   | nothing = nothing
...   | just (ag , bg , eg , s₂ , n₂) with unify fuelD s₂ bg bf
...     | nothing = nothing
...     | just s₃ =
          just ((if ef ∨ eg then PEff ag cf else (ag P⇒[ Many ] cf)) , n₂ , s₃)

-- pInfer/destructFinish are a top-level mutual pair (NOT a where) so
-- the canon-invariance proof (CanonPrincipal) can reason about
-- destructFinish as a first-class function.
mutual
  pInfer : Imports → SchemaCtx → Env → RawExpr → ℕ → PSubst → Result
  pInfer imps sch env (Raw.RVar x) n s with lookupEnv x env
  ... | just t  = just (t , n , s)
  ... | nothing = liftName (lookupName imps sch x n) s
  pInfer imps sch env (Raw.RResolved cn) n s =
    liftName (lookupName imps sch (canonKey cn) n) s
  pInfer imps sch env (Raw.RApp f x) n s = pInferApp imps sch env f x n s
  pInfer imps sch env (Raw.RLam x body) n s =
    pInfer imps sch ((x , PTVar (mv n)) ∷ env) body (suc n) s >>=R λ { (tb , n₁ , s₁) →
    just ((PTVar (mv n) P⇒[ Many ] tb) , n₁ , s₁) }
  pInfer imps sch env (Raw.RLet x e₁ e₂) n s =
    pInfer imps sch env e₁ n s >>=R λ { (t₁ , n₁ , s₁) →
    pInfer imps sch ((x , t₁) ∷ env) e₂ n₁ s₁ }
  pInfer imps sch env (Raw.RPair a b) n s =
    pInfer imps sch env a n s >>=R λ { (ta , n₁ , s₁) →
    pInfer imps sch env b n₁ s₁ >>=R λ { (tb , n₂ , s₂) →
    just ((ta P* tb) , n₂ , s₂) } }
  pInfer imps sch env (Raw.RDestruct e x e₁ y e₂) n s =
    pInfer imps sch env e n s >>=R λ { (te , n₁ , s₁) →
    destructFinish imps sch env x e₁ y e₂ te n₁ s₁ }
  pInfer imps sch env Raw.RUnit n s = just (PUnit , n , s)
  pInfer imps sch env (Raw.RInt _) n s = just (PInt , n , s)
  pInfer imps sch env (Raw.RStringLit _) n s = just (PStr , n , s)
  pInfer imps sch env (Raw.RAnnot e T) n s with typeToPoly T
  ... | nothing = nothing
  ... | just tT =
        pInfer imps sch env e n s >>=R λ { (te , n₁ , s₁) →
        retTy tT n₁ (unify fuelD s₁ te tT) }
  pInfer imps sch env (Raw.RBinOp op a b) n s =
    pInfer imps sch env a n s >>=R λ { (ta , n₁ , s₁) →
    retTy PInt n₁ (unify fuelD s₁ ta PInt) >>=R λ { (_ , _ , s₂) →
    pInfer imps sch env b n₁ s₂ >>=R λ { (tb , n₂ , s₃) →
    retTy (if isComparisonOp op then (PUnit P+ PUnit) else PInt) n₂
          (unify fuelD s₃ tb PInt) } } }
  pInfer imps sch env (Raw.RUnaryOp _ a) n s =
    pInfer imps sch env a n s >>=R λ { (ta , n₁ , s₁) →
    retTy PInt n₁ (unify fuelD s₁ ta PInt) }
  -- Not covered in v1 (signature required): qualified-unresolved refs,
  -- cata/In/ana (functor metavariables).
  pInfer _ _ _ _ _ _ = nothing

  -- | Application dispatch. `compose f g` is grade-polymorphic, so it
  -- is special-cased — via an explicit `≟` on the head name (NOT a
  -- string-literal pattern), so proofs can case on abstract head names
  -- (the literal-pattern-opacity fix, same as `classifyAppHeadView`).
  pInferApp : Imports → SchemaCtx → Env → RawExpr → RawExpr → ℕ → PSubst → Result
  -- D136: `compose` arrives as `RResolved (gen "compose")` now. The bare-`RVar`
  -- head is kept for a lexical binder named `compose`, where the special
  -- treatment must NOT fire — hence `false` rather than a `≟` on the name.
  pInferApp imps sch env f@(Raw.RApp (Raw.RResolved cn) f') g n s =
    pInferAppB imps sch env f f' g n s (isYes (cn ≟ᶜ gen "compose"))
  pInferApp imps sch env f x n s = pAppGen imps sch env f x n s

  -- | Bool-dispatched continuation of `pInferApp` (with-free so the
  -- termination checker sees only pattern variables, and proofs can
  -- case on the Bool). `f` is the WHOLE head, `f'` compose's first arm.
  pInferAppB : Imports → SchemaCtx → Env → RawExpr → RawExpr → RawExpr → ℕ → PSubst
             → Bool → Result
  pInferAppB imps sch env f f' g n s true =
    pInfer imps sch env f' n s >>=R λ { (tf , n₁ , s₁) →
    pInfer imps sch env g n₁ s₁ >>=R λ { (tg , n₂ , s₂) →
    composeFinish tf tg n₂ s₂ } }
  pInferAppB imps sch env f f' g n s false = pAppGen imps sch env f g n s

  pAppGen : Imports → SchemaCtx → Env → RawExpr → RawExpr → ℕ → PSubst → Result
  pAppGen imps sch env f x n s =
    pInfer imps sch env f n s >>=R λ { (tf , n₁ , s₁) →
    pInfer imps sch env x n₁ s₁ >>=R λ { (tx , n₂ , s₂) →
    appFinish tf tx n₂ s₂ } }

  destructFinish : Imports → SchemaCtx → Env → String → RawExpr → String → RawExpr
                 → PolyType → ℕ → PSubst → Result
  destructFinish imps sch env x e₁ y e₂ te n₁ s₁
    with unify fuelD s₁ te (PTVar (mv n₁) P+ PTVar (mv (suc n₁)))
  ... | nothing = nothing
  ... | just s₂ =
        pInfer imps sch ((x , PTVar (mv n₁)) ∷ env) e₁ (suc (suc n₁)) s₂ >>=R
          λ { (t₁ , n₂ , s₃) →
        pInfer imps sch ((y , PTVar (mv (suc n₁))) ∷ env) e₂ n₂ s₃ >>=R
          λ { (t₂ , n₃ , s₄) →
        retTy t₁ n₃ (unify fuelD s₄ t₁ t₂) } }

------------------------------------------------------------------------
-- Definition-boundary finalization
------------------------------------------------------------------------

-- | Rename leftover metavariables `?k` to presentation variables
-- `t0, t1, …` (generalization: they become the schema's PTVars).
renameVars : PolyType → PolyType
renameVars t = proj₁ (freshen' t 0 [])
  where
  letter : ℕ → String
  letter k = "t" ++ showℕ k
  mutual
    freshen' : PolyType → ℕ → List (String × String)
             → PolyType × ℕ × List (String × String)
    freshen' (PTVar x) k acc with lookupRen x acc
    ... | just y  = PTVar y , k , acc
    ... | nothing = PTVar (letter k) , suc k , (x , letter k) ∷ acc
    freshen' (a P* b) k acc =
      let (a' , k₁ , acc₁) = freshen' a k acc
          (b' , k₂ , acc₂) = freshen' b k₁ acc₁
      in a' P* b' , k₂ , acc₂
    freshen' (a P+ b) k acc =
      let (a' , k₁ , acc₁) = freshen' a k acc
          (b' , k₂ , acc₂) = freshen' b k₁ acc₁
      in a' P+ b' , k₂ , acc₂
    freshen' (a P⇒[ q ] b) k acc =
      let (a' , k₁ , acc₁) = freshen' a k acc
          (b' , k₂ , acc₂) = freshen' b k₁ acc₁
      in a' P⇒[ q ] b' , k₂ , acc₂
    freshen' (PEff a b) k acc =
      let (a' , k₁ , acc₁) = freshen' a k acc
          (b' , k₂ , acc₂) = freshen' b k₁ acc₁
      in PEff a' b' , k₂ , acc₂
    freshen' (Pμ-type F) k acc =
      let (F' , k₁ , acc₁) = freshenF' F k acc in Pμ-type F' , k₁ , acc₁
    freshen' (Pν-type F) k acc =
      let (F' , k₁ , acc₁) = freshenF' F k acc in Pν-type F' , k₁ , acc₁
    freshen' u k acc = u , k , acc

    freshenF' : PolyFunctor → ℕ → List (String × String)
              → PolyFunctor × ℕ × List (String × String)
    freshenF' (PK A) k acc =
      let (A' , k₁ , acc₁) = freshen' A k acc in PK A' , k₁ , acc₁
    freshenF' PId k acc = PId , k , acc
    freshenF' (F P⊕ G) k acc =
      let (F' , k₁ , acc₁) = freshenF' F k acc
          (G' , k₂ , acc₂) = freshenF' G k₁ acc₁
      in F' P⊕ G' , k₂ , acc₂
    freshenF' (F P⊗ G) k acc =
      let (F' , k₁ , acc₁) = freshenF' F k acc
          (G' , k₂ , acc₂) = freshenF' G k₁ acc₁
      in F' P⊗ G' , k₂ , acc₂

-- | Ground-or-schema split of a zonked type (top-level, expr-free —
-- the canon-invariance proof needs `principal` to be a composition of
-- expr-independent finalizers around `pInfer`).
groundOr : PolyType → Maybe (Type ⊎ PolyType)
groundOr t' with isGround t'
... | inj₁ g = just (inj₁ (extractGround t' g))
... | inj₂ _ = just (inj₂ (renameVars t'))

finishP : Result → Maybe (Type ⊎ PolyType)
finishP nothing = nothing
finishP (just (t , _ , s)) = groundOr (zonk fuelD s t)

-- | THE oracle. `inj₁` = the body's principal type is ground; `inj₂` =
-- it is a proper schema (generalize at the def boundary — route to the
-- telescope). `nothing` = no type found (genuinely untypeable, or a v1
-- coverage gap): ask for a signature.
principal : NamedCtx → RawExpr → Maybe (Type ⊎ PolyType)
principal ctx e =
  finishP (pInfer (NamedCtx.imports ctx) (projSchemas (NamedCtx.polys ctx))
             [] e 0 [])

pgProj : Maybe (Type ⊎ PolyType) → Maybe Type
pgProj (just (inj₁ T)) = just T
pgProj _ = nothing

-- | Ground-only projection (the M2 wiring point).
principalGround : NamedCtx → RawExpr → Maybe Type
principalGround ctx e = pgProj (principal ctx e)

pgSchema : Maybe (Type ⊎ PolyType) → Maybe PolyType
pgSchema (just (inj₂ pty)) = just pty
pgSchema _ = nothing

-- | The M3 routing criterion: a sig-less definition whose body has a
-- NON-ground principal type in the EMPTY context (builtins + literals
-- only — no imports, no earlier defs; those bodies are ground or
-- unknown here and keep the FunInfo path). `just pty` ⇒ the def is a
-- telescope entry with schema `pty`, exactly like a signed poly def.
-- Used by BOTH `extractFunctions-go` (Parser) and `polyDefNames`
-- (Resolve) so the two classifications agree definitionally.
siglessSchema : RawExpr → Maybe PolyType
siglessSchema body = pgSchema (principal emptyCtx body)
