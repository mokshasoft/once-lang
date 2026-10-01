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
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

open import Once.Type using (Type)
open import Once.Type.Rigid using (RigidFree)
import Once.Compile as C
open C.FunInfo using (funName)
open C.PolyFunInfo using (pfunName)
open import Once.TypeCheck.Classify using (Imports; NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
import Once.TypeCheck.Elaborate
import Once.TypeCheck.Classify
import Once.Parser
import Once.Parser.Module.Core as P
import Once.Adequacy.NameClash as NC
import Data.String.Properties as StrProp
import Relation.Nullary
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Type
import Once.Surface.Context as Ctx
open import Once.TypeCheck.Classify using (PolyCtx; lookupPolyPrefix)
open import Once.Denotation.Realize using (realize)
open import Once.Adequacy.SourceTrace using (irFunOf; tableOf-go)
open import Once.Denotation.Program using (IRFun)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.Surface.Elaborate using (elaborateFull)

-- A declaration-import map that agrees with the scope's telescope entries.
IAgree : (String → Imports) → List (C.PolyFunInfo × C.FunCtx) → Set
IAgree I tele = All (λ q → I (pfunName (proj₁ q)) ≡ proj₂ q) tele

-- The scope's imports are rigid-free.
ImportsRF : Imports → Set
ImportsRF imps = ∀ {x T} → Once.TypeCheck.Classify.lookupImport imps x ≡ just T → RigidFree T

irf-cons : ∀ {imps : Imports} {y : String} {ty : Type} → RigidFree ty → ImportsRF imps → ImportsRF ((y , ty) ∷ imps)
irf-cons {y = y} g old {x} lk with y ≟str x
... | yes _ = subst RigidFree (just-injective lk) g
... | no _  = old lk

-- The remaining entries' names: distinct, and new to the scope.
entryName : C.Entry → String
entryName = Once.Parser.entryNameOf

scopeNames : C.CScope → List String
scopeNames csc = map proj₁ (C.CScope.cimps csc) ++ map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc)

Fresh : C.CScope → List C.Entry → Set
Fresh csc es = AllPairs _≢_ (map entryName es) × All (λ x → All (x ≢_) (scopeNames csc)) (map entryName es)

------------------------------------------------------------------------
-- The declaration imports along the telescope
------------------------------------------------------------------------

declImps-head : ∀ (e : C.PolyFunInfo × C.FunCtx) (es : List (C.PolyFunInfo × C.FunCtx))
                  (d : Dec (pfunName (proj₁ e) ≡ pfunName (proj₁ e)))
              → C.declImps-aux e es (pfunName (proj₁ e)) d ≡ proj₂ e
declImps-head e es (yes _) = refl
declImps-head e es (no ¬p) = ⊥-elim (¬p refl)

declImps-skip : ∀ (e : C.PolyFunInfo × C.FunCtx) (es : List (C.PolyFunInfo × C.FunCtx)) (x : String)
                  (d : Dec (pfunName (proj₁ e) ≡ x)) → pfunName (proj₁ e) ≢ x
              → C.declImps-aux e es x d ≡ C.declImps es x
declImps-skip e es x (yes p) ne = ⊥-elim (ne p)
declImps-skip e es x (no _)  ne = refl

iself-step : ∀ (e : C.PolyFunInfo × C.FunCtx) (tele : List (C.PolyFunInfo × C.FunCtx)) (qs : List (C.PolyFunInfo × C.FunCtx))
           → All (pfunName (proj₁ e) ≢_) (map (λ q → pfunName (proj₁ q)) qs)
           → IAgree (C.declImps tele) qs → IAgree (C.declImps (e ∷ tele)) qs
iself-step e tele []       []       []       = []
iself-step e tele (q ∷ qs) (h ∷ hs) (a ∷ as) =
  trans (declImps-skip e tele (pfunName (proj₁ q)) (pfunName (proj₁ e) ≟str pfunName (proj₁ q)) h) a ∷ iself-step e tele qs hs as

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

fresh-fun : ∀ {csc fi ty es} → Fresh csc (C.e-fun fi ∷ es) → Fresh (C.extendScope csc (funName fi) ty) es
fresh-fun {csc} {es = es} ((hd ∷ tl) , (_ ∷ hs)) = tl , insert-all [] (scopeNames csc) (map entryName es) hd hs

fresh-poly : ∀ {csc pfi es} → Fresh csc (C.e-poly pfi ∷ es) → Fresh (C.addEntry csc pfi) es
fresh-poly {csc} {es = es} ((hd ∷ tl) , (_ ∷ hs)) =
  tl , insert-all (map proj₁ (C.CScope.cimps csc)) (map (λ q → pfunName (proj₁ q)) (C.CScope.ctele csc))
                  (map entryName es) hd hs

-- The checker's derivation, read off its verified result.
sound-of : ∀ {ctx : Once.TypeCheck.Classify.NamedCtx} {e : _} {T : Type} {Ψ se d f}
             (cr : Once.TypeCheck.Elaborate.VerifiedCheckResult ctx e T)
         → proj₁ cr ≡ Once.TypeCheck.Elaborate.success Ψ se d f → ctx ⊢ᶜ e ∶ T ⨾ Ψ
sound-of (Once.TypeCheck.Elaborate.success _ _ _ _ , w) refl = w


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
entries-distinct : ∀ (m : P.Module) {es : List C.Entry}
  → C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → AllPairs _≢_ (map entryName es)
entries-distinct (P.mkModule ds) eq = NC.guard-entries (C.extractFunctions-go (C.extractAliases (P.mkModule ds)) ds C.nothing) eq

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
irFun-main : ∀ (ctx : C.FunCtx) (polys : Once.TypeCheck.Classify.PolyCtx) (impsOf : String → C.FunCtx)
               (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋} {r : _}
               (v : _) → C.compileFun-main-aux C.Heap false ctx polys impsOf x ty body v ≡ inj₂ irFun
           → C.compileFunBody C.Heap false ctx polys impsOf x ty body ≡ r → r ≡ inj₂ irFun
irFun-main ctx polys impsOf x ty body (inj₁ _) () _
irFun-main ctx polys impsOf x ty body (inj₂ _) cf eq = trans (sym eq) cf

irFun-body : ∀ (ctx : C.FunCtx) (polys : Once.TypeCheck.Classify.PolyCtx) (impsOf : String → C.FunCtx)
               (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋} (b : Bool)
           → C.compileFun-aux C.Heap false ctx polys impsOf x ty body b ≡ inj₂ irFun
           → C.compileFunBody C.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
irFun-body ctx polys impsOf x ty body true  cf = irFun-main ctx polys impsOf x ty body (C.validateMain ty) cf refl
irFun-body ctx polys impsOf x ty body false cf = cf

aux-form : ∀ (ctx : C.FunCtx) (polys : Once.TypeCheck.Classify.PolyCtx) (impsOf : String → C.FunCtx)
             (x : String) (ty : Type) {body : _} {se : _} {d f : ℕ}
             (cr : Once.TypeCheck.Elaborate.VerifiedCheckResult (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty)
             (ce : proj₁ cr ≡ Once.TypeCheck.Elaborate.success Ctx.Usage.[] se d f)
         → C.compileFunBody-aux C.Heap false ctx polys impsOf x ty refl cr
           ≡ inj₂ (elaborateFull C.Heap (resolveExpr polys impsOf ((x , ty) ∷ ctx) 0 (realize (sound-of cr ce))))
aux-form ctx polys impsOf x ty (Once.TypeCheck.Elaborate.success _ _ _ _ , w) refl = refl

irFun-form : ∀ (ctx : C.FunCtx) (polys : Once.TypeCheck.Classify.PolyCtx) (impsOf : String → C.FunCtx)
               (x : String) (ty : Type) (body : _) {irFun : IR ⌊ Once.Type.Unit ⌋ ⌊ ty ⌋}
               {se : _} {d f : ℕ}
           → C.compileFun C.Heap false ctx polys impsOf x ty body ≡ inj₂ irFun
           → (ce : Once.TypeCheck.Elaborate.checkElab (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty
                     ≡ Once.TypeCheck.Elaborate.success Ctx.Usage.[] se d f)
           → irFun ≡ elaborateFull C.Heap (resolveExpr polys impsOf ((x , ty) ∷ ctx) 0
                       (realize (sound-of (Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty) ce)))
irFun-form ctx polys impsOf x ty body cf ce =
  inj₂-injective (trans (sym (irFun-body ctx polys impsOf x ty body (Relation.Nullary.isYes (x ≟str "main")) cf))
                        (aux-form ctx polys impsOf x ty (Once.TypeCheck.Elaborate.checkElabV (Once.TypeCheck.Classify.ctxWithImportsAndPolys ctx polys) body ty) ce))

