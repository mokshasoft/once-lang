-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprLinked — plan 0.146 B1.7 (D457): THE BRIDGE'S PROGRAM IS
-- GRADED, from the compile pipeline.
--
-- Each definition's source (`CompileSrc.srcEntries`) refers only to earlier
-- definitions, each at its declared type, so at its definition's grade
-- (`GradeIn`); with the table's names distinct, the bridge's resolver finds
-- a reference at no other grade (`ExprTable.GradedBodies`, `MainGraded`), and
-- the sources' FFI references are declared (`ExprOps.Table.SrcsOK`).
--
-- The walk is `ProgramLinked`'s, in lockstep with master's bundle, over the
-- sources' table; its splice step is `ProgramLinked.poly-tel` at `GradeIn`.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)

module Once.LinCore.ExprLinked (fmt : TargetNum) (ans : FFIAnswers) where

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; _==_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
import Data.List.Relation.Unary.All
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; []; _∷_; length)

open import Once.Spec.Type using (Type; Ty)
import Once.Spec.Context as SC
import Once.Spec.Surface.Syntax as Syn
open import Once.IR using (IR; Heap)
open import Once.IRTy using (⌊_⌋)
open import Once.TypeCheck.Scope using (NamedCtx; PolyCtx)
open import Once.TypeCheck.Classify using (TopCtx; ctxWithImportsAndPolys)
import Once.TypeCheck.Elaborate as TE
open import Once.TypeCheck.Link using (resolveExpr)
open import Once.Type.DecEq using (_≟T_)
open import Once.Compile using (validateMain)
open import Once.CompileSrc
  using (Src; src; module Src; mapSrc; srcM; srcFun; srcFunI; src-aux; src-main-aux; srcI-aux; srcI-main-aux;
         srcBody; srcBody-aux; srcBodyI; srcBodyI-aux; srcBodyI-at)
import Once.Adequacy.FunBundle as FB

------------------------------------------------------------------------
-- 1. A CHECKED DEFINITION'S SOURCE: its resolved term, unoptimized.
------------------------------------------------------------------------

-- the source a successful chain returns
srcOf : ∀ {ty} {ir : IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋} (r : String ⊎ Src ty) → mapSrc r ≡ inj₂ ir → Src ty
srcOf (inj₂ s) _ = s
srcOf (inj₁ _) ()

srcOf-eq : ∀ {ty} {ir : IR ⌊ Once.Spec.Type.Unit {0} ⌋ ⌊ ty ⌋} (r : String ⊎ Src ty) (e : mapSrc r ≡ inj₂ ir) → r ≡ inj₂ (srcOf r e)
srcOf-eq (inj₂ s) _ = refl
srcOf-eq (inj₁ _) ()

module SrcForm (ctx : TopCtx) (polys : PolyCtx) (impsOf : String → TopCtx) (x : String) (ty : Type) (body : Syn.Expr) where
  private
    Γc = NamedCtx.debruijn (ctxWithImportsAndPolys ctx polys)
    uf = (x , ty) ∷ TopCtx.tdefs ctx

  -- `main`'s check passes before its body
  src-body : ∀ (b : Bool) {s} → src-aux Heap false ctx polys impsOf x ty body b ≡ inj₂ s
           → srcBody Heap false ctx polys impsOf x ty body ≡ inj₂ s
  src-body true {s} e = main (validateMain ty) e
    where
      main : (v : String ⊎ ⊤) → src-main-aux Heap false ctx polys impsOf x ty body v ≡ inj₂ s
           → srcBody Heap false ctx polys impsOf x ty body ≡ inj₂ s
      main (inj₁ _) ()
      main (inj₂ _) e′ = e′
  src-body false e = e

  src-bodyI : ∀ (b : Bool) {s} → srcI-aux Heap false ctx polys impsOf x ty body b ≡ inj₂ s
            → srcBodyI Heap false ctx polys impsOf x ty body ≡ inj₂ s
  src-bodyI true {s} e = main (validateMain ty) e
    where
      main : (v : String ⊎ ⊤) → srcI-main-aux Heap false ctx polys impsOf x ty body v ≡ inj₂ s
           → srcBodyI Heap false ctx polys impsOf x ty body ≡ inj₂ s
      main (inj₁ _) ()
      main (inj₂ _) e′ = e′
  src-bodyI false e = e

  body-form : ∀ {se d f} (cr : TE.CheckElabResult Γc ty) → cr ≡ TE.success SC.[] se d f
            → srcBody-aux Heap false ctx polys impsOf x ty refl cr ≡ inj₂ (src refl Heap false (resolveExpr polys impsOf uf 0 se))
  body-form (TE.success _ _ _ _) refl = refl

  bodyI-form : ∀ {se d f} (cr : TE.InferElabResult Γc) → cr ≡ TE.success ty SC.[] se d f
             → srcBodyI-aux Heap false ctx polys impsOf x ty refl cr ≡ inj₂ (src refl Heap false (resolveExpr polys impsOf uf 0 se))
  bodyI-form {se = se} (TE.success _ _ _ _ _) refl = at (ty ≟T ty)
    where
      at : (dd : Dec (ty ≡ ty))
         → srcBodyI-at se Heap false ctx polys impsOf x ty refl dd ≡ inj₂ (src refl Heap false (resolveExpr polys impsOf uf 0 se))
      at (yes refl) = refl
      at (no ¬p)    = ⊥-elim (¬p refl)

  -- ★ a checked definition's source is its checker term, resolved, unoptimized
  src-form : ∀ (ft : Maybe Type) {s se d f} → srcM ft Heap false ctx polys impsOf x ty body ≡ inj₂ s
           → FB.ElabOK ft (ctxWithImportsAndPolys ctx polys) body ty SC.[] se d f
           → s ≡ src refl Heap false (resolveExpr polys impsOf uf 0 se)
  src-form (just _) cf ce = inj₂-injective (trans (sym (src-body (x == "main") cf)) (body-form _ ce))
  src-form nothing  cf ce = inj₂-injective (trans (sym (src-bodyI (x == "main") cf)) (bodyI-form _ ce))

------------------------------------------------------------------------
-- 2. ★ A REFERENCE AT ITS DEFINITION'S GRADE: an earlier definition of the
-- name, whose grade is the reference's key grade (`ExprTable.GradedRef`'s).
------------------------------------------------------------------------

open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Induction using (<-wellFounded)
open import Once.CompileSrc using (CompiledSrc; mkCompiledSrc; module CompiledSrc; srcEntries; consCS; compileFunM-src;
                                   se-fun; se-prim; se-prim-conc; se-mono; se-mono-p; se-mono-src; se-poly-main; se-poly-p; se-poly)
open CompiledSrc using (csName; csType; csSrc)
open import Once.Spec.Name using (bare)
import Once.Spec.Grade as G
import Once.Spec.Type as ST
open import Once.Spec.Type using (_⇒[_]_; ∅ₖ)
open import Once.LinCore.Core fmt using (Gr; act)
open import Once.LinCore.FromIR fmt using (grade)
import Once.LinCore.ExprTable
module ET = Once.LinCore.ExprTable fmt ans
open import Once.Contract using (ISig)
open import Once.TypeCheck.Scope using (Imports; lookupImport)
open import Once.TypeCheck.Classify using (ctxAt; baseKinds)
open import Once.TypeCheck.ElaborateSound using (checkElabV; inferElabV; checkSoundOf; soundOf)
open import Once.Weaken using (wk₀-id)
import Once.Compile as C
import Once.Parser as Parser
open Parser.FunInfo using (funName; funType; funBody; funIsPrimitive)
open Parser.PolyFunInfo using (pfunName)
open import Once.Module using (ModTele; []; ffi; mono; poly; teleSig)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
import Once.Core.Translate as TR
import Once.Adequacy.ModuleProgram as MP
import Once.Adequacy.AcceptSound as AS
open import Data.Fin using (zero)
open import Once.Adequacy.TelePosition
  using (IAgree; Fresh; scopeNames; declImps-head; iself-step; ++⁻ʳ; fresh-head; fresh-sig; fresh-fun; fresh-poly)
open import Once.Adequacy.ProgramLinked using (SpliceOKR; spliceWith; poly-tel; resolve-refs; imp-defsR; sig-cons)
open import Once.Adequacy.ElaborateLinked using (DeclIn; Refs-map)
open import Once.Denotation.SurfaceRefs using (Refs; FFIRef; ImpRef; PolyRef; InScope)
import Data.String.Properties as SProp

-- a reference's key grade
refGr : ∀ {m} → Ty m → Gr
refGr (A ⇒[ G.mk-kind q π ] B) = grade π
refGr ST.Unit       = act
refGr ST.Void       = act
refGr (X ST.* Y)    = act
refGr (X ST.+ Y)    = act
refGr (ST.μ F)      = act
refGr (ST.ν F f)    = act
refGr ST.Int        = act
refGr ST.Float      = act
refGr (ST.var i)    = act

-- a definition's grade is its type's key grade
dcGr-ref : ∀ (T : Type) → ET.dcGr T ≡ refGr T
dcGr-ref (A ⇒[ G.mk-kind q π ] B) = refl
dcGr-ref ST.Unit       = refl
dcGr-ref ST.Void       = refl
dcGr-ref (X ST.* Y)    = refl
dcGr-ref (X ST.+ Y)    = refl
dcGr-ref (ST.μ F)      = refl
dcGr-ref (ST.ν F f)    = refl
dcGr-ref ST.Int        = refl
dcGr-ref ST.Float      = refl
dcGr-ref (ST.var ())

GradeIn : List CompiledSrc → ∀ {m} → String → Ty m → Set
GradeIn pre x A = Any (λ c → (csName c ≡ bare x) × (ET.dcGr (csType c) ≡ refGr A)) pre

module Walk (σ : ISig) where

  -- each definition, over the ones before it: unoptimized, its references graded, its FFI declared
  Bodies : List CompiledSrc → Set
  Bodies []       = ⊤
  Bodies (c ∷ cs) = Bodies cs × (Src.opt (csSrc c) ≡ false) × Refs (DeclIn σ) (GradeIn cs) (GradeIn cs) (Src.expr (csSrc c))

  record TInv (csc : C.CScope) (pre : List CompiledSrc) : Set where
    field
      iself  : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
      imp-ok : ∀ {x} {A : Type} → lookupImport (C.CScope.cimps csc) x ≡ just A → GradeIn pre x A
      tel-ok : ∀ (I : String → TopCtx) → IAgree I (C.CScope.ctele csc)
             → ∀ {x} {A : Type} → PolyRef (C.cpolys csc) ∅ₖ x A → SpliceOKR (DeclIn σ) (λ {m} → GradeIn pre {m}) (C.cpolys csc) I x A
      bod-ok : Bodies pre
      sig-ok : ∀ {x} {A : Type} → lookupImport (C.CScope.csig csc) x ≡ just A → (x , A) ∈ σ

  -- a reference to an import, at its ground type
  imp-refT : ∀ {csc pre} → TInv csc pre → ∀ {A : Type} {x} → ImpRef (C.CScope.cimps csc) x A → GradeIn pre x A
  imp-refT {pre = pre} inv {x = x} (T , lk , e) = subst (GradeIn pre x) (sym (trans e (wk₀-id T))) (TInv.imp-ok inv lk)

  -- the table grows
  splice-there : ∀ {c pre polys I x} {A : Type} → SpliceOKR (DeclIn σ) (λ {m} → GradeIn pre {m}) polys I x A
               → SpliceOKR (DeclIn σ) (λ {m} → GradeIn (c ∷ pre) {m}) polys I x A
  splice-there {c} {pre} {polys} {I} {x} {A} sp {s} {b} {pre′} lk ac uf fresh {Γ = Γ} =
    Refs-map {Ps = DeclIn σ} {Ps′ = DeclIn σ} {Pc = GradeIn pre} {Pp = GradeIn pre} {Pc′ = GradeIn (c ∷ pre)} {Pp′ = GradeIn (c ∷ pre)}
             (λ r → r) there there
             (spliceWith {Γ = Γ} pre′ ac I uf fresh x A (checkElabV (ctxAt baseKinds (I x) pre′) b A))
             (sp lk ac uf fresh {Γ = Γ})

  -- an FFI declaration joins Σ
  tinv-sig : ∀ {csc pre} (x : String) (ty : Type) → (x , ty) ∈ σ → TInv csc pre → TInv (C.extendSig csc x ty) pre
  tinv-sig x ty d inv = record
    { iself  = TInv.iself inv
    ; imp-ok = TInv.imp-ok inv
    ; tel-ok = TInv.tel-ok inv
    ; bod-ok = TInv.bod-ok inv
    ; sig-ok = sig-cons x ty d (TInv.sig-ok inv)
    }

  -- a definition joins the scope, its source the table
  tinv-entry : ∀ {csc pre} (x : String) (ty : Type) (s : Src ty)
             → Src.opt s ≡ false → Refs (DeclIn σ) (GradeIn pre) (GradeIn pre) (Src.expr s)
             → TInv csc pre → TInv (C.extendScope csc x ty) (mkCompiledSrc (bare x) ty s ∷ pre)
  tinv-entry {csc} {pre} x ty s o r inv = record
    { iself  = TInv.iself inv
    ; imp-ok = imp-defsR (x == "main") {R = GradeIn pre} {R′ = GradeIn (c ∷ pre)} x ty (here (refl , dcGr-ref ty)) there (TInv.imp-ok inv)
    ; tel-ok = λ I ia pr → splice-there {c = c} {pre = pre} {polys = C.cpolys csc} {I = I} (TInv.tel-ok inv I ia pr)
    ; bod-ok = TInv.bod-ok inv , o , r
    ; sig-ok = TInv.sig-ok inv
    }
    where c = mkCompiledSrc (bare x) ty s

  -- a telescope entry joins the scope (`ProgramLinked.poly-tel` at `GradeIn`)
  tinv-poly : ∀ {Σ : Signature} {s} {S : Defs s} {csc pre} {pfi : Parser.PolyFunInfo}
              (ss : TR.SigSig Σ (C.CScope.csig csc)) (is : TR.ImpSig Σ S (C.CScope.cimps csc))
              (ts : TR.TeleSig Σ S (C.telePolys (C.CScope.ctele csc))) (N : MP.Names Σ S (C.CScope.csig csc) is ts)
            → MP.PolyWit Σ (AS.scopeOf csc) pfi SC.[]
            → Data.List.Relation.Unary.All.All (pfunName pfi ≢_) (scopeNames csc)
            → TInv csc pre → TInv (C.addEntry csc pfi) pre
  tinv-poly {csc = csc} {pre} {pfi} ss is ts N W fr inv = record
    { iself  = declImps-head (pfi , C.ctop csc) (C.CScope.ctele csc) (pfunName pfi SProp.≟ pfunName pfi)
               Data.List.Relation.Unary.All.∷ iself-step (pfi , C.ctop csc) (C.CScope.ctele csc) (C.CScope.ctele csc)
                            (++⁻ʳ (Data.List.map proj₁ (C.CScope.cimps csc)) fr) (TInv.iself inv)
    ; imp-ok = TInv.imp-ok inv
    ; tel-ok = poly-tel (λ {m} → GradeIn pre {m}) ss is ts N W (TInv.sig-ok inv) (imp-refT inv) (TInv.tel-ok inv)
    ; bod-ok = TInv.bod-ok inv
    ; sig-ok = TInv.sig-ok inv
    }

  ----------------------------------------------------------------------
  -- 3. ★ THE WALK, in lockstep with master's bundle and `srcEntries`
  ----------------------------------------------------------------------

  -- the checker's term refers only into its scope (its witness says so)
  inScope : ∀ (ft : Maybe Type) (ctx : NamedCtx 0) (body : Syn.Expr) (ty : Type) {Ψ se d f}
          → FB.ElabOK ft ctx body ty Ψ se d f → InScope ctx se
  inScope (just _) ctx body ty ce = proj₁ (subst (checkSoundOf ctx body ty) ce (proj₂ (checkElabV ctx body ty)))
  inScope nothing  ctx body ty ce = proj₁ (subst (soundOf ctx body) ce (proj₂ (inferElabV ctx body)))

  -- ★ a definition's source, checked in its scope: unoptimized, its references graded
  body-refs : ∀ {csc pre} → TInv csc pre → (ft : Maybe Type) (x : String) (ty : Type) {body : Syn.Expr} {s : Src ty} → ∀ {se d f}
            → srcM ft Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ s
            → FB.ElabOK ft (FB.ctxC csc) body ty SC.[] se d f
            → (Src.opt s ≡ false) × Refs (DeclIn σ) (GradeIn pre) (GradeIn pre) (Src.expr s)
  body-refs {csc} {pre} inv ft x ty {body} {se = se} cf ce =
    subst (λ s′ → (Src.opt s′ ≡ false) × Refs (DeclIn σ) (GradeIn pre) (GradeIn pre) (Src.expr s′))
          (sym (SrcForm.src-form (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ft cf ce))
          (refl , resolve-refs (λ {m} → GradeIn pre {m}) (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
                    (TInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (TInv.iself inv))
                    (<-wellFounded (length (C.cpolys csc))) ((x , ty) ∷ TopCtx.tdefs (C.ctop csc)) 0 se
                    (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef (C.CScope.cimps csc)}
                              {Pp = PolyRef (C.cpolys csc) ∅ₖ} {Pc′ = GradeIn pre} {Pp′ = PolyRef (C.cpolys csc) ∅ₖ}
                              (TInv.sig-ok inv) (imp-refT inv) (λ r → r) se (inScope ft (FB.ctxC csc) body ty ce)))

  cons-inv : ∀ (c : CompiledSrc) (r : String ⊎ List CompiledSrc) {srcs} → consCS c r ≡ inj₂ srcs
           → Σ (List CompiledSrc) (λ rest → (r ≡ inj₂ rest) × (srcs ≡ c ∷ rest))
  cons-inv c (inj₁ _)    ()
  cons-inv c (inj₂ rest) refl = rest , refl , refl

  walk : ∀ {Σ : Signature} {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es)
           {k} {S : Defs k} (ss : TR.SigSig Σ (C.CScope.csig csc)) (is : TR.ImpSig Σ S (C.CScope.cimps csc))
           (ts : TR.TeleSig Σ S (C.telePolys (C.CScope.ctele csc))) (N : MP.Names Σ S (C.CScope.csig csc) is ts) (F : MP.Fresh Σ N es)
           (pre : List CompiledSrc)
       → TInv csc pre → Fresh csc es
       → (∀ {d} → d ∈ teleSig mt → d ∈ σ) → TR.SigIn Σ mt
       → ∀ {srcs} → srcEntries Heap false csc es ≡ inj₂ srcs → Bodies (ET.srcOrder srcs pre)
  walk [] FB.bnil ss is ts N F pre inv fr u uΣ refl = TInv.bod-ok inv
  walk {csc = csc} {es = Parser.e-fun fi ∷ es} (ffi {ty = ty} ep et cc hh rest) (FB.bffi {ty = ty′} ep′ et′ ec eh rest-b)
       ss is ts N F pre inv fr u uΣ {srcs} hyp =
    walk rest (proj₁ packed) (TR.s-ffi cc hh (uΣ (here refl)) ss) is ts (MP.names-ffi _ fi ty F) (MP.fresh-ffi _ fi ty F) pre
         (tinv-sig (funName fi) ty (u (here refl)) inv) (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr)
         (λ m → u (there m)) (λ m → uΣ (there m)) (proj₂ packed)
    where
      h₃ : srcEntries Heap false (C.extendSig csc (funName fi) ty′) es ≡ inj₂ srcs
      h₃ = trans (cong₂ (se-prim-conc Heap false csc fi es ty′) (sym ec) (sym eh))
                 (trans (cong (se-prim Heap false csc fi es) (sym et′))
                        (trans (cong (se-fun Heap false csc fi es) (sym ep′)) hyp))
      packed : FB.FunBundle (C.extendSig csc (funName fi) ty) es × (srcEntries Heap false (C.extendSig csc (funName fi) ty) es ≡ inj₂ srcs)
      packed = subst (λ T → FB.FunBundle (C.extendSig csc (funName fi) T) es × (srcEntries Heap false (C.extendSig csc (funName fi) T) es ≡ inj₂ srcs))
                     (just-injective (trans (sym et′) et)) (rest-b , h₃)
  walk (ffi {fi = Parser.mkFunInfo x ft bd prim} refl et cc hh rest) (FB.bcons () rf fc ce cf rest-b) ss is ts N F pre inv fr u uΣ hyp
  walk {Σ = Σ} {csc = csc} {es = Parser.e-poly pfi ∷ es} (poly {Ψ = SC.[]} pr W rest) (FB.bpoly fc ce rest-b) ss is ts N F pre inv fr u uΣ {srcs} hyp =
    walk rest rest-b ss (TR.wkI Σ is) (TR.t-def zero refl (TR.wkT Σ ts)) (MP.names-polyF Σ pfi F) (MP.fresh-poly Σ pfi F) pre
         (tinv-poly ss is ts N W (fresh-head {csc = csc} {e = Parser.e-poly pfi} {es = es} fr) inv)
         (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr) u uΣ (poly-src (pfunName pfi SProp.≟ "main") hyp)
    where
      poly-src : ∀ (dm : Dec (pfunName pfi ≡ "main")) → se-poly-main Heap false csc pfi es dm ≡ inj₂ srcs
               → srcEntries Heap false (C.addEntry csc pfi) es ≡ inj₂ srcs
      poly-src (yes _) ()
      poly-src (no _)  h =
        trans (cong (λ r → se-poly Heap false csc pfi es (C.checkOK r)) (sym ce)) (trans (cong (se-poly-p Heap false csc pfi es) (sym fc)) h)
  walk {Σ = Σ} {csc = csc} {es = Parser.e-fun fi ∷ es} (mono {ty = ty} refl er pr _ rest)
       (FB.bcons {ty = ty′} {Ψ = SC.[]} {irFun = irFun} refl rf fc ce cf rest-b) ss is ts N F pre inv fr u uΣ {srcs} hyp =
    subst (λ l → Bodies (ET.srcOrder l pre)) (sym (proj₂ (proj₂ ci)))
      (walk rest (proj₁ packed) ss (TR.impDefs Σ (funName fi == "main") is) (TR.wkT Σ ts)
            (MP.names-monoF Σ (funName fi == "main") fi ty F) (MP.fresh-mono Σ (funName fi == "main") fi ty F) (c ∷ pre)
            (proj₂ (proj₂ packed)) (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr) u uΣ (proj₁ (proj₂ packed)))
    where
      sM = srcM (funType fi) Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) (funName fi) ty′ (funBody fi)
      e′ : mapSrc sM ≡ inj₂ irFun
      e′ = trans (sym (compileFunM-src (funType fi) Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) (funName fi) ty′ (funBody fi))) cf
      s = srcOf sM e′
      sm : sM ≡ inj₂ s
      sm = srcOf-eq sM e′
      c = mkCompiledSrc (bare (funName fi)) ty′ s
      h₃ : consCS c (srcEntries Heap false (C.extendScope csc (funName fi) ty′) es) ≡ inj₂ srcs
      h₃ = trans (cong (se-mono-src Heap false csc fi es ty′) (sym sm))
                 (trans (cong (se-mono-p Heap false csc fi es ty′) (sym fc))
                        (trans (cong (se-mono Heap false csc fi es) (sym rf)) hyp))
      ci = cons-inv c (srcEntries Heap false (C.extendScope csc (funName fi) ty′) es) h₃
      br = body-refs inv (funType fi) (funName fi) ty′ sm ce
      P : Type → Set
      P T = FB.FunBundle (C.extendScope csc (funName fi) T) es
            × (srcEntries Heap false (C.extendScope csc (funName fi) T) es ≡ inj₂ (proj₁ ci))
            × TInv (C.extendScope csc (funName fi) T) (c ∷ pre)
      packed : P ty
      packed = subst P (inj₂-injective (trans (sym rf) er))
                     (rest-b , proj₁ (proj₂ ci) , tinv-entry (funName fi) ty′ s (proj₁ br) (proj₂ br) inv)
