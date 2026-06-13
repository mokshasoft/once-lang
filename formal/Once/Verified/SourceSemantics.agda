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
open import Data.Integer using (ℤ; _+_; _-_; _*_; -_) renaming (∣_∣ to absℤ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)

open import Once.TypeCheck.Raw as Raw
  using (RawExpr; RVar; RQualified; RApp; RLam; RLet; RPair; RDestruct;
         RUnit; RInt; RStringLit; RAnnot; RBinOp; RUnaryOp;
         BinOp; OpAdd; OpSub; OpMul; UnaryOp; OpNeg)
open import Once.Parser.Module.Core as Mod using (Module; Decl; DFunDef)
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
-- optimisation only). NOTE (Plan 0.45 follow-up): div/mod and the
-- comparison ops are placeholders for now — only +,-,* are faithful.
------------------------------------------------------------------------

binResult : BinOp → Value → Value → Result
binResult OpAdd (Vint a) (Vint b) = just (Vint (a + b) , [])
binResult OpSub (Vint a) (Vint b) = just (Vint (a - b) , [])
binResult OpMul (Vint a) (Vint b) = just (Vint (a * b) , [])
binResult _     (Vint a) (Vint b) = just (Vint (a + b) , [])   -- TODO: div/mod/compare
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

runTrace : Module → ℕ → List SigOpEvent
runTrace m n with extractDefs (Mod.Module.decls m)
... | defs with lookupDef defs "main"
...   | nothing   = []
...   | just body with eval n defs [] body
...     | nothing       = []
...     | just (_ , ev) = ev
