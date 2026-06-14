-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceSemantics — the SOURCE-LEVEL reference semantics
-- (Plan 0.45 Part A). A small, direct, fuel-bounded interpreter over the
-- RAW surface (`RawExpr`) that says "these are the SigOp calls this
-- program makes, in order" — computed INDEPENDENTLY of the elaborator,
-- so the whole compile (typechecker included) is verified to preserve it.
--
-- This is `sourceTrace`'s engine. It must stay much smaller than the
-- ~2400-line elaborator and structurally unlike it (no type inference,
-- no closure records, no codegen) — otherwise it just moves the trust.
--
-- Design (see Plan 0.45 discussion):
--   * Untyped `Value` datatype with DEFUNCTIONALISED closures (`Vclos`),
--     because a HOAS `Vfun : (Value → Value) → Value` is not strictly
--     positive (Value in a negative position).
--   * `eval` takes FUEL (ℕ) for termination; `Behavior = ℕ → List
--     SigOpEvent` uses that fuel as its step index.
--   * SigOp application is the SOLE emitter (mirrors `obs`); arith is
--     PURE (the arith→SigOp lowering is an internal optimisation only);
--     events are concatenated in evaluation order.
------------------------------------------------------------------------

module Once.Verified.SourceSemantics where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; _+_; _-_; _*_; -_; _≤ᵇ_) renaming (∣_∣ to absℤ)
open import Data.Integer.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RApp; RLam; RLet; RPair; RDestruct;
         RUnit; RInt; RStringLit; RAnnot; RBinOp; RUnaryOp;
         BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
         OpLt; OpLe; OpGt; OpGe; OpEq; OpNe; UnaryOp; OpNeg)
open import Once.Parser.Module.Core as Mod
  using (Module; Decl; DFunDef; DTypeSig; DSignature; DTypeAlias; DImport)
open import Once.Verified.Trace using (SigOpEvent; mk-event)

------------------------------------------------------------------------
-- Runtime values. Defunctionalised: a function is a closure (captured
-- environment + parameter name + body), never an Agda function — so
-- `Value` stays strictly positive.
------------------------------------------------------------------------

-- The CCC generators exposed as surface names. Classified once (string
-- dispatch via `classifyB`), then matched as a datatype downstream.
data BTag : Set where
  bId bFst bSnd bInl bInr bIn bOut bCompose bCase bCata bTerminal : BTag

data Value : Set where
  Vint   : ℤ → Value
  Vstr   : String → Value
  Vunit  : Value
  Vpair  : Value → Value → Value
  Vinl   : Value → Value
  Vinr   : Value → Value
  Vin    : Value → Value                              -- μ-constructor `In`
  Vclos  : List (String × Value) → String → RawExpr → Value
  -- a partially-applied builtin / SigOp: head + args collected so far
  Vbuiltin : BTag → List Value → Value
  Vsigop   : String → List Value → Value

Env : Set
Env = List (String × Value)

-- A run produces a value (when fuel suffices) together with the SigOp
-- events emitted while producing it, in order.
Result : Set
Result = Maybe (Value × List SigOpEvent)

------------------------------------------------------------------------
-- Environment lookup.
------------------------------------------------------------------------

lookupEnv : Env → String → Maybe Value
lookupEnv []             _ = nothing
lookupEnv ((y , v) ∷ ρ) x with x ≟str y
... | yes _ = just v
... | no  _ = lookupEnv ρ x

-- The argument of a SigOp call, as `Maybe ℕ` (the `SigOpEvent` shape):
-- an Int argument is observed as its ℕ magnitude, anything else as
-- `nothing` (mirrors `mkEvent`, which records `just n` only for `Int`).
argℕ : Value → Maybe ℕ
argℕ (Vint z) = just (absℤ z)
argℕ _        = nothing

------------------------------------------------------------------------
-- Result plumbing: a writer-style bind threading events in order.
------------------------------------------------------------------------

_>>=ᵣ_ : Result → (Value → Result) → Result
nothing       >>=ᵣ _ = nothing
just (v , e₁) >>=ᵣ k with k v
... | nothing        = nothing
... | just (v′ , e₂) = just (v′ , e₁ ++ e₂)

prependEv : List SigOpEvent → Result → Result
prependEv _  nothing       = nothing
prependEv e₁ (just (v , e₂)) = just (v , e₁ ++ e₂)

------------------------------------------------------------------------
-- Arithmetic — PURE (no event; the arith→SigOp lowering is an internal
-- optimisation only). Mirrors `evalSurface`: comparisons return a sum
-- (`Vinl tt` = true / `Vinr tt` = false). `divℤ`/`modℤ` are the language's
-- div/mod primitives — postulated here as in `Surface.Semantics`
-- ("axiom — actual impl handles div-by-zero"); their agreement with the
-- value semantics' is a Part-B faithfulness obligation.
------------------------------------------------------------------------

postulate
  divℤ modℤ : ℤ → ℤ → ℤ

boolToSum : Bool → Value
boolToSum true  = Vinl Vunit
boolToSum false = Vinr Vunit

binResult : BinOp → Value → Value → Result
binResult OpAdd (Vint a) (Vint b) = just (Vint (a + b) , [])
binResult OpSub (Vint a) (Vint b) = just (Vint (a - b) , [])
binResult OpMul (Vint a) (Vint b) = just (Vint (a * b) , [])
binResult OpDiv (Vint a) (Vint b) = just (Vint (divℤ a b) , [])
binResult OpMod (Vint a) (Vint b) = just (Vint (modℤ a b) , [])
binResult OpLt  (Vint a) (Vint b) = just (boolToSum (not (b ≤ᵇ a)) , [])  -- a<b ≡ ¬(b≤a)
binResult OpLe  (Vint a) (Vint b) = just (boolToSum (a ≤ᵇ b) , [])
binResult OpGt  (Vint a) (Vint b) = just (boolToSum (not (a ≤ᵇ b)) , [])  -- a>b ≡ ¬(a≤b)
binResult OpGe  (Vint a) (Vint b) = just (boolToSum (b ≤ᵇ a) , [])        -- a≥b ≡ b≤a
binResult OpEq  (Vint a) (Vint b) = just (boolToSum (does (a ≟ b)) , [])
binResult OpNe  (Vint a) (Vint b) = just (boolToSum (not (does (a ≟ b))) , [])
binResult _     _        _        = nothing

------------------------------------------------------------------------
-- Builtin (CCC generator) name classification — string dispatch in ONE
-- place (a table), so the interpreter matches a datatype downstream.
------------------------------------------------------------------------

btable : List (String × BTag)
btable = ("id" , bId) ∷ ("fst" , bFst) ∷ ("snd" , bSnd)
       ∷ ("inl" , bInl) ∷ ("inr" , bInr) ∷ ("In" , bIn) ∷ ("Out" , bOut)
       ∷ ("compose" , bCompose) ∷ ("case" , bCase) ∷ ("cata" , bCata)
       ∷ ("terminal" , bTerminal) ∷ []

classifyB : String → Maybe BTag
classifyB x = go btable
  where go : List (String × BTag) → Maybe BTag
        go [] = nothing
        go ((y , t) ∷ ts) with x ≟str y
        ... | yes _ = just t
        ... | no  _ = go ts

-- A non-local, non-user-fn name: a CCC generator, else a SigOp.
resolveName : String → Value
resolveName x with classifyB x
... | just t  = Vbuiltin t []
... | nothing = Vsigop x []

------------------------------------------------------------------------
-- Top-level user functions (`DFunDef name _ body`).
------------------------------------------------------------------------

Defs : Set
Defs = List (String × RawExpr)

extractDefs : List Decl → Defs
extractDefs []                          = []
extractDefs (DFunDef nm _ body ∷ ds)    = (nm , body) ∷ extractDefs ds
extractDefs (_ ∷ ds)                    = extractDefs ds

lookupDef : Defs → String → Maybe RawExpr
lookupDef []            _ = nothing
lookupDef ((y , b) ∷ ds) x with x ≟str y
... | yes _ = just b
... | no  _ = lookupDef ds x

-- SOURCE-SIDE half of `main-exists-align`: a `DFunDef "main"` present in the
-- decls ⇒ `lookupDef (extractDefs ds) "main"` finds a body. Pure induction over
-- the decls — prepending any decl can only ADD a front hit, never remove the
-- tail hit, and `extractDefs` skips every non-`DFunDef`. The compiler side
-- (`main-exists-align`) supplies the `Any` witness (a "main" `CompiledFun`
-- traces back to a `DFunDef "main"` in `decls`).
lookup-main-of-dfundef :
  ∀ (ds : List Decl)
  → Any (λ d → ∃[ al ] ∃[ bd ] d ≡ DFunDef "main" al bd) ds
  → ∃[ body ] lookupDef (extractDefs ds) "main" ≡ just body
lookup-main-of-dfundef [] ()
lookup-main-of-dfundef (d ∷ ds) (here (al , bd , refl)) with "main" ≟str "main"
... | yes _  = bd , refl
... | no ¬p  = ⊥-elim (¬p refl)
lookup-main-of-dfundef (DFunDef nm al bd  ∷ ds) (there a') with "main" ≟str nm
... | yes _  = bd , refl
... | no  _  = lookup-main-of-dfundef ds a'
lookup-main-of-dfundef (DTypeSig _ _      ∷ ds) (there a') = lookup-main-of-dfundef ds a'
lookup-main-of-dfundef (DSignature _ _ _  ∷ ds) (there a') = lookup-main-of-dfundef ds a'
lookup-main-of-dfundef (DTypeAlias _ _ _  ∷ ds) (there a') = lookup-main-of-dfundef ds a'
lookup-main-of-dfundef (DImport _         ∷ ds) (there a') = lookup-main-of-dfundef ds a'

------------------------------------------------------------------------
-- The interpreter. Fuel-bounded; `Behavior = ℕ → List SigOpEvent` uses
-- the fuel as its step index.
------------------------------------------------------------------------

mutual
  eval : ℕ → Defs → Env → RawExpr → Result
  eval zero    _    _ _ = nothing
  eval (suc f) defs ρ (RVar x) with lookupEnv ρ x
  ... | just v  = just (v , [])
  ... | nothing with lookupDef defs x
  ...   | just body = eval f defs [] body
  ...   | nothing   = just (resolveName x , [])
  eval (suc f) defs ρ (RQualified nm _) = just (Vsigop nm [] , [])
  eval (suc f) defs ρ (RApp g x) =
    eval f defs ρ g >>=ᵣ λ vg → eval f defs ρ x >>=ᵣ λ vx → apply f defs vg vx
  eval (suc f) defs ρ (RLam x body)  = just (Vclos ρ x body , [])
  eval (suc f) defs ρ (RLet x e1 e2) =
    eval f defs ρ e1 >>=ᵣ λ v1 → eval f defs ((x , v1) ∷ ρ) e2
  eval (suc f) defs ρ (RPair a b) =
    eval f defs ρ a >>=ᵣ λ va → eval f defs ρ b >>=ᵣ λ vb → just (Vpair va vb , [])
  eval (suc f) defs ρ (RDestruct s xl l yr r) with eval f defs ρ s
  ... | nothing            = nothing
  ... | just (Vinl a , e₁) = prependEv e₁ (eval f defs ((xl , a) ∷ ρ) l)
  ... | just (Vinr b , e₁) = prependEv e₁ (eval f defs ((yr , b) ∷ ρ) r)
  ... | just (_ , _)       = nothing
  eval (suc f) defs ρ RUnit          = just (Vunit , [])
  eval (suc f) defs ρ (RInt n)       = just (Vint n , [])
  eval (suc f) defs ρ (RStringLit s) = just (Vstr s , [])
  eval (suc f) defs ρ (RAnnot e _)   = eval f defs ρ e
  eval (suc f) defs ρ (RBinOp op a b) =
    eval f defs ρ a >>=ᵣ λ va → eval f defs ρ b >>=ᵣ λ vb → binResult op va vb
  eval (suc f) defs ρ (RUnaryOp OpNeg e) =
    eval f defs ρ e >>=ᵣ λ v → neg v
    where neg : Value → Result
          neg (Vint z) = just (Vint (- z) , [])
          neg _        = nothing

  apply : ℕ → Defs → Value → Value → Result
  apply zero    _    _ _ = nothing
  apply (suc f) defs (Vclos ρ x body)  v = eval f defs ((x , v) ∷ ρ) body
  apply (suc f) defs (Vbuiltin t args) v = applyBuiltin f defs t (args ++ (v ∷ []))
  apply (suc f) defs (Vsigop nm _)     v = just (Vunit , mk-event nm (argℕ v) ∷ [])
  apply (suc f) defs _                 _ = nothing

  -- Builtins compute at saturation, else collect the arg (partial app).
  applyBuiltin : ℕ → Defs → BTag → List Value → Result
  applyBuiltin f defs bId       (v ∷ [])               = just (v , [])
  applyBuiltin f defs bFst      (Vpair a b ∷ [])       = just (a , [])
  applyBuiltin f defs bSnd      (Vpair a b ∷ [])       = just (b , [])
  applyBuiltin f defs bInl      (v ∷ [])               = just (Vinl v , [])
  applyBuiltin f defs bInr      (v ∷ [])               = just (Vinr v , [])
  applyBuiltin f defs bIn       (v ∷ [])               = just (Vin v , [])
  applyBuiltin f defs bOut      (Vin v ∷ [])           = just (v , [])
  applyBuiltin f defs bTerminal (_ ∷ [])               = just (Vunit , [])
  applyBuiltin f defs bCompose  (g ∷ h ∷ x ∷ [])       = apply f defs h x >>=ᵣ λ hx → apply f defs g hx
  applyBuiltin f defs bCase     (l ∷ r ∷ Vinl a ∷ [])  = apply f defs l a
  applyBuiltin f defs bCase     (l ∷ r ∷ Vinr b ∷ [])  = apply f defs r b
  applyBuiltin f defs bCata     (alg ∷ mu ∷ [])        = cataFold f defs alg mu
  applyBuiltin f defs t         args                   = just (Vbuiltin t args , [])

  -- Catamorphism: fold a μ-value. Recursive positions are exactly the
  -- `Vin`-wrapped sub-values (In marks them), so no functor witness is
  -- needed at runtime — `mapIn` recurses the fold into them.
  cataFold : ℕ → Defs → Value → Value → Result
  cataFold zero    _    _   _          = nothing
  cataFold (suc f) defs alg (Vin layer) =
    mapIn f defs alg layer >>=ᵣ λ layer′ → apply f defs alg layer′
  cataFold (suc f) defs _   _          = nothing

  mapIn : ℕ → Defs → Value → Value → Result
  mapIn zero    _    _   _           = nothing
  mapIn (suc f) defs alg (Vin c)     = cataFold f defs alg (Vin c)
  mapIn (suc f) defs alg (Vpair a b) =
    mapIn f defs alg a >>=ᵣ λ a′ → mapIn f defs alg b >>=ᵣ λ b′ → just (Vpair a′ b′ , [])
  mapIn (suc f) defs alg (Vinl a)    = mapIn f defs alg a >>=ᵣ λ a′ → just (Vinl a′ , [])
  mapIn (suc f) defs alg (Vinr a)    = mapIn f defs alg a >>=ᵣ λ a′ → just (Vinr a′ , [])
  mapIn (suc f) defs _   v           = just (v , [])

------------------------------------------------------------------------
-- The trace of a module: run `main`'s body with fuel `n`, return the
-- emitted SigOp events. `Behavior = ℕ → List SigOpEvent`.
------------------------------------------------------------------------

-- Explicit-`Maybe` helpers (no nested `with`), so reduction reasoning about
-- `runTrace` — `no-main-empty` (lookupDef nothing ⇒ []) and the per-RawExpr
-- trace core — can match the option directly instead of fighting with-opacity.
runTraceEval : Result → List SigOpEvent
runTraceEval nothing        = []
runTraceEval (just (_ , ev)) = ev

runTraceMain : ℕ → Defs → Maybe RawExpr → List SigOpEvent
runTraceMain n defs nothing     = []
runTraceMain n defs (just body) = runTraceEval (eval n defs [] body)

runTrace : Module → ℕ → List SigOpEvent
runTrace m n =
  let defs = extractDefs (Mod.Module.decls m)
  in runTraceMain n defs (lookupDef defs "main")

-- Source side of `no-main-empty` (Plan 0.45 Part B): no `main` definition ⇒
-- the empty trace, for every fuel. `runTraceMain … nothing` reduces to `[]`
-- (explicit-`Maybe` helper, no with-opacity).
runTrace-no-main :
  ∀ (m : Module) (n : ℕ)
  → lookupDef (extractDefs (Mod.Module.decls m)) "main" ≡ nothing
  → runTrace m n ≡ []
runTrace-no-main m n eq rewrite eq = refl

-- With-main characterization (the dual): when `main` is defined, `runTrace`
-- is exactly the trace of evaluating its body. Together with `runTrace-no-main`
-- this fully reduces `runTrace` to `eval` of the main body — the source-side
-- half of `elaborate-preserves-trace` (Plan 0.45 #10).
runTrace-main :
  ∀ (m : Module) (n : ℕ) (body : RawExpr)
  → lookupDef (extractDefs (Mod.Module.decls m)) "main" ≡ just body
  → runTrace m n ≡ runTraceEval (eval n (extractDefs (Mod.Module.decls m)) [] body)
runTrace-main m n body eq rewrite eq = refl
