-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TelePosition — the position predicates of a walk over the
-- module telescope, in lockstep with the compile walk (`compileEntries`):
-- the declaration imports, the rigid-freeness of the scope's imports, and the
-- freshness of the remaining entries' names (D249). Shared by the meaning walk
-- (`TeleWalk`) and the linkedness walk (`ProgramLinked`); none of it depends
-- on the target's number format.
------------------------------------------------------------------------

module Once.Adequacy.TelePosition where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
import Data.String as Str
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Once.Internal.Type using (Type)
open import Once.Internal.Type.WellFormed using (RigidFree)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser
open Parser.FunInfo using (funName)
open Parser.PolyFunInfo using (pfunName)
open import Once.Internal.Typing.Scope using (Imports)
open import Once.Internal.Typing using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_)
open import Once.Internal.Type.DecEq using (_≟T_)
import Once.TypeCheck.Elaborate
import Once.Internal.Typing.Scope
import Once.TypeCheck.Classify
import Once.Parser
import Once.Parser.Module as Module
import Once.Parser.Module.Core as P
import Data.Maybe as Maybe
import Once.Adequacy.NameClash as NC
import Data.String.Properties as StrProp
import Relation.Nullary
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Internal.Type
import Once.Type
import Once.Internal.Context as Ctx
open import Once.Internal.Typing.Scope using (PolyCtx; lookupPolyPrefix)
open import Once.TypeCheck.Classify using (TopCtx)
open import Once.Denotation.Realize using (realize; realize-infer)
open import Once.Compile using (irFunOf; tableOf-go)
open import Once.Denotation.Program using (IRFun)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.Surface.Elaborate using (elaborateFull)

-- A declaration-import map that agrees with the scope's telescope entries.
IAgree : (String → TopCtx) → List (Parser.PolyFunInfo × TopCtx) → Set
IAgree I tele = All (λ q → I (pfunName (proj₁ q)) ≡ proj₂ q) tele

-- The scope's imports are rigid-free.
ImportsRF : Imports → Set
ImportsRF imps = ∀ {x T} → Once.Internal.Typing.Scope.lookupImport imps x ≡ just T → RigidFree T

irf-cons : ∀ {imps : Imports} {y : String} {ty : Type} → RigidFree ty → ImportsRF imps → ImportsRF ((y , ty) ∷ imps)
irf-cons {y = y} g old {x} lk with y Str.≟ x
... | yes _ = subst RigidFree (just-injective lk) g
... | no _  = old lk

-- D324: the definitions' context, `main` left out (`C.extendDefs`).
irf-defs : ∀ (b : Bool) {imps : Imports} {y : String} {ty : Type} → RigidFree ty → ImportsRF imps
         → ImportsRF (C.extendDefs-at b imps y ty)
irf-defs true  {imps} {y} {ty} g old = old
irf-defs false {imps} {y} {ty} g old = irf-cons {imps} {y} {ty} g old

-- The remaining entries' names: distinct, and new to the scope.
entryName : Parser.Entry → String
entryName = Once.Parser.entryNameOf

scopeNames : C.CScope → List String
scopeNames csc = map proj₁ (C.CScope.cimps csc) ++ map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)

Fresh : C.CScope → List Parser.Entry → Set
Fresh csc es = AllPairs _≢_ (map entryName es) × All (λ x → All (x ≢_) (scopeNames csc)) (map entryName es)

------------------------------------------------------------------------
-- The declaration imports along the telescope
------------------------------------------------------------------------

declImps-head : ∀ (e : Parser.PolyFunInfo × TopCtx) (es : List (Parser.PolyFunInfo × TopCtx))
                  (d : Dec (pfunName (proj₁ e) ≡ pfunName (proj₁ e)))
              → C.declImps-aux e es (pfunName (proj₁ e)) d ≡ proj₂ e
declImps-head e es (yes _) = refl
declImps-head e es (no ¬p) = ⊥-elim (¬p refl)

declImps-skip : ∀ (e : Parser.PolyFunInfo × TopCtx) (es : List (Parser.PolyFunInfo × TopCtx)) (x : String)
                  (d : Dec (pfunName (proj₁ e) ≡ x)) → pfunName (proj₁ e) ≢ x
              → C.declImps-aux e es x d ≡ C.declImps es x
declImps-skip e es x (yes p) ne = ⊥-elim (ne p)
declImps-skip e es x (no _)  ne = refl

iself-step : ∀ (e : Parser.PolyFunInfo × TopCtx) (tele : List (Parser.PolyFunInfo × TopCtx)) (qs : List (Parser.PolyFunInfo × TopCtx))
           → All (pfunName (proj₁ e) ≢_) (map (λ q → pfunName (proj₁ q)) qs)
           → IAgree (C.declImps tele) qs → IAgree (C.declImps (e ∷ tele)) qs
iself-step e tele []       []       []       = []
iself-step e tele (q ∷ qs) (h ∷ hs) (a ∷ as) =
  trans (declImps-skip e tele (pfunName (proj₁ q)) (pfunName (proj₁ e) Str.≟ pfunName (proj₁ q)) h) a ∷ iself-step e tele qs hs as

++⁻ʳ : ∀ {x : String} (as : List String) {bs : List String} → All (x ≢_) (as ++ bs) → All (x ≢_) bs
++⁻ʳ []       a        = a
++⁻ʳ (_ ∷ as) (_ ∷ a) = ++⁻ʳ as a

------------------------------------------------------------------------
-- Freshness along the walk
------------------------------------------------------------------------

private
  insert-ne : ∀ (as bs : List String) {y x : String} → y ≢ x → All (y ≢_) (as ++ bs) → All (y ≢_) (as ++ x ∷ bs)
  insert-ne []       bs ne hs       = ne ∷ hs
  insert-ne (a ∷ as) bs ne (h ∷ hs) = h ∷ insert-ne as bs ne hs

  insert-all : ∀ (as bs : List String) {x : String} (ys : List String) → All (x ≢_) ys
             → All (λ y → All (y ≢_) (as ++ bs)) ys → All (λ y → All (y ≢_) (as ++ x ∷ bs)) ys
  insert-all as bs []       []         []         = []
  insert-all as bs (y ∷ ys) (ne ∷ nes) (h ∷ hs) = insert-ne as bs (λ e → ne (sym e)) h ∷ insert-all as bs ys nes hs

fresh-head : ∀ {csc e es} → Fresh csc (e ∷ es) → All (entryName e ≢_) (scopeNames csc)
fresh-head (_ , (h ∷ _)) = h

-- D324: `main` does not enter the scope, which then stays as it was.
fresh-fun-at : ∀ (b : Bool) {csc fi ty es} → Fresh csc (Parser.e-fun fi ∷ es)
             → Fresh (C.cscope (C.CScope.csig csc) (C.extendDefs-at b (C.CScope.cimps csc) (funName fi) ty) (C.CScope.ctele csc)) es
fresh-fun-at true  ((_ ∷ tl) , (_ ∷ hs)) = tl , hs
fresh-fun-at false {csc} {es = es} ((hd ∷ tl) , (_ ∷ hs)) = tl , insert-all [] (scopeNames csc) (map entryName es) hd hs

fresh-fun : ∀ {csc fi ty es} → Fresh csc (Parser.e-fun fi ∷ es) → Fresh (C.extendScope csc (funName fi) ty) es
fresh-fun {csc} {fi} {ty} {es} = fresh-fun-at (funName fi Str.== "main") {csc} {fi} {ty} {es}

-- D274: an FFI declaration extends Σ, not the definitions' names.
fresh-sig : ∀ {csc fi ty es} → Fresh csc (Parser.e-fun fi ∷ es) → Fresh (C.extendSig csc (funName fi) ty) es
fresh-sig ((_ ∷ tl) , (_ ∷ hs)) = tl , hs

fresh-poly : ∀ {csc pfi es} → Fresh csc (Parser.e-poly pfi ∷ es) → Fresh (C.addEntry csc pfi) es
fresh-poly {csc} {es = es} ((hd ∷ tl) , (_ ∷ hs)) =
  tl , insert-all (map proj₁ (C.CScope.cimps csc)) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc))
                  (map entryName es) hd hs

-- The checker's derivation, read off its verified result.
sound-of : ∀ {ctx : Once.Internal.Typing.Scope.NamedCtx} {e : _} {T : Type} {Ψ se d f}
             (cr : Once.TypeCheck.Elaborate.VerifiedCheckResult ctx e T)
         → proj₁ cr ≡ Once.TypeCheck.Elaborate.success Ψ se d f → ctx ⊢ᶜ e ∶ T ⨾ Ψ
sound-of (Once.TypeCheck.Elaborate.success _ _ _ _ , w) refl = w

-- R8: the synthesizer's derivation, read off its verified result.
sound-of-i : ∀ {ctx : Once.Internal.Typing.Scope.NamedCtx} {e : _} {T : Type} {Ψ se d f}
               (cr : Once.TypeCheck.Elaborate.VerifiedInferResult ctx e)
           → proj₁ cr ≡ Once.TypeCheck.Elaborate.success T Ψ se d f → ctx ⊢ᵢ e ∶ T ⨾ Ψ
sound-of-i (Once.TypeCheck.Elaborate.success _ _ _ _ _ , w) refl = w


------------------------------------------------------------------------
-- The telescope's lookup
------------------------------------------------------------------------

lookup-skip : ∀ (n : String) {s b} (L : PolyCtx) (y : String) → n ≢ y
  → lookupPolyPrefix ((n , s , b) ∷ L) y ≡ lookupPolyPrefix L y
lookup-skip n L y n≢y with StrProp._≟_ n y
... | yes p = ⊥-elim (n≢y p)
... | no _  = refl

lookup-head : ∀ (n : String) {s b} (L : PolyCtx)
  → lookupPolyPrefix ((n , s , b) ∷ L) n ≡ just (s , b , L)
lookup-head n L with StrProp._≟_ n n
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

------------------------------------------------------------------------
-- The walk's start: the empty scope, and the entries' names (D249)
------------------------------------------------------------------------

-- The walk's premises at the start: the empty scope, and the entries' names
-- (D249: the extractor's guard).
entries-distinct : ∀ (m : P.Module) {es : List Parser.Entry}
  → Parser.extractFunctions (Parser.extractAliases m) m ≡ inj₂ es → AllPairs _≢_ (map entryName es)
entries-distinct (P.mkModule ds) eq = NC.guard-entries (Parser.thenExtract (Parser.sigsAdjacent ds Maybe.nothing) (Parser.extractFunctions-go (Parser.extractAliases (P.mkModule ds)) (Parser.sigsFirst ds) Maybe.nothing)) eq

none-in-empty : ∀ (xs : List String) → All (λ x → All (x ≢_) (scopeNames C.emptyCScope)) xs
none-in-empty []       = []
none-in-empty (x ∷ xs) = [] ∷ none-in-empty xs


------------------------------------------------------------------------
-- The table the compile walk builds (latest first)
------------------------------------------------------------------------

tableOf-go-++ : ∀ (cfs : List C.CompiledFun) (xs pre : List IRFun) → tableOf-go cfs (xs ++ pre) ≡ tableOf-go cfs xs ++ pre
tableOf-go-++ []         xs pre = refl
tableOf-go-++ (cf ∷ cfs) xs pre = tableOf-go-++ cfs (irFunOf cf ∷ xs) pre

------------------------------------------------------------------------
-- What the compile walk emits for a definition
------------------------------------------------------------------------

-- A definition compiles to its resolved body's elaboration (D253: `main`
-- too — its type check passes, and it is not rewritten).
irFun-main : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
               (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Internal.Type.Unit ⌋ ⌊ ty ⌋} {r : _}
               (v : _) → C.compileFun-main-aux IR.Heap false ctx polys impsOf x ty body v ≡ inj₂ irFun
           → C.compileFunBody IR.Heap false ctx polys impsOf x ty body ≡ r → r ≡ inj₂ irFun
irFun-main ctx polys impsOf x ty body (inj₁ _) () _
irFun-main ctx polys impsOf x ty body (inj₂ _) cf eq = trans (sym eq) cf

irFun-body : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
               (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Internal.Type.Unit ⌋ ⌊ ty ⌋} (b : Bool)
           → C.compileFun-aux IR.Heap false ctx polys impsOf x ty body b ≡ inj₂ irFun
           → C.compileFunBody IR.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
irFun-body ctx polys impsOf x ty body true  cf = irFun-main ctx polys impsOf x ty body (C.validateMain ty) cf refl
irFun-body ctx polys impsOf x ty body false cf = cf

aux-form : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
             (x : String) (ty : Type) {body : _} {se : _} {d f : ℕ}
             (cr : Once.TypeCheck.Elaborate.VerifiedCheckResult (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty)
             (ce : proj₁ cr ≡ Once.TypeCheck.Elaborate.success Ctx.Usage.[] se d f)
         → C.compileFunBody-aux IR.Heap false ctx polys impsOf x ty refl cr
           ≡ inj₂ (elaborateFull IR.Heap (resolveExpr polys impsOf ((x , ty) ∷ TopCtx.tdefs ctx) 0 (realize (sound-of cr ce))))
aux-form ctx polys impsOf x ty (Once.TypeCheck.Elaborate.success _ _ _ _ , w) refl = refl

irFun-form : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
               (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Internal.Type.Unit ⌋ ⌊ ty ⌋}
               {se : _} {d f : ℕ}
           → C.compileFun IR.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
           → (ce : Once.TypeCheck.Elaborate.checkElab (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty
                     ≡ Once.TypeCheck.Elaborate.success Ctx.Usage.[] se d f)
           → irFun ≡ elaborateFull IR.Heap (resolveExpr polys impsOf ((x , ty) ∷ TopCtx.tdefs ctx) 0
                       (realize (sound-of (Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty) ce)))
irFun-form ctx polys impsOf x ty body cf ce =
  inj₂-injective (trans (sym (irFun-body ctx polys impsOf x ty body (Relation.Nullary.isYes (x Str.≟ "main")) cf))
                        (aux-form ctx polys impsOf x ty (Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty) ce))

-- R8: a definition without a signature compiles to its synthesized body's
-- elaboration.
irFunI-body : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
                (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Internal.Type.Unit ⌋ ⌊ ty ⌋} (b : Bool)
            → C.compileFunI-aux IR.Heap false ctx polys impsOf x ty body b ≡ inj₂ irFun
            → C.compileFunBodyI IR.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
irFunI-body ctx polys impsOf x ty body {irFun} true  cf = main (C.validateMain ty) cf
  where
    main : (v : _) → C.compileFunI-main-aux IR.Heap false ctx polys impsOf x ty body v ≡ inj₂ irFun
         → C.compileFunBodyI IR.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
    main (inj₁ _) ()
    main (inj₂ _) e = e
irFunI-body ctx polys impsOf x ty body false cf = cf

auxI-form : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
              (x : String) (ty : Type) {body : _} {se : _} {d f : ℕ}
              (cr : Once.TypeCheck.Elaborate.VerifiedInferResult (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body)
              (ce : proj₁ cr ≡ Once.TypeCheck.Elaborate.success ty Ctx.Usage.[] se d f)
          → C.compileFunBodyI-aux IR.Heap false ctx polys impsOf x ty refl cr
            ≡ inj₂ (elaborateFull IR.Heap (resolveExpr polys impsOf ((x , ty) ∷ TopCtx.tdefs ctx) 0 (realize-infer (sound-of-i cr ce))))
auxI-form ctx polys impsOf x ty (Once.TypeCheck.Elaborate.success _ _ _ _ _ , w) refl = at (ty ≟T ty)
  where
    at : (dd : Dec (ty ≡ ty))
       → C.compileFunBodyI-at IR.Heap false ctx polys impsOf x ty refl w dd
         ≡ inj₂ (elaborateFull IR.Heap (resolveExpr polys impsOf ((x , ty) ∷ TopCtx.tdefs ctx) 0 (realize-infer w)))
    at (yes refl) = refl
    at (no ¬p)    = ⊥-elim (¬p refl)

irFun-formI : ∀ (ctx : TopCtx) (polys : Once.Internal.Typing.Scope.PolyCtx) (impsOf : String → TopCtx)
                (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Internal.Type.Unit ⌋ ⌊ ty ⌋}
                {se : _} {d f : ℕ}
            → C.compileFunI IR.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
            → (ce : Once.TypeCheck.Elaborate.inferElab (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body
                      ≡ Once.TypeCheck.Elaborate.success ty Ctx.Usage.[] se d f)
            → irFun ≡ elaborateFull IR.Heap (resolveExpr polys impsOf ((x , ty) ∷ TopCtx.tdefs ctx) 0
                        (realize-infer (sound-of-i (Once.TypeCheck.Elaborate.inferElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body) ce)))
irFun-formI ctx polys impsOf x ty body cf ce =
  inj₂-injective (trans (sym (irFunI-body ctx polys impsOf x ty body (Relation.Nullary.isYes (x Str.≟ "main")) cf))
                        (auxI-form ctx polys impsOf x ty (Once.TypeCheck.Elaborate.inferElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body) ce))

