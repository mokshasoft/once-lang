-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ModuleProgram — a typed module's core program (plan 0.103
-- phase 6c; plan 0.122 §5.6, stage e).
--
-- Walking the module in declaration order (`Once.Core.Translate` relates
-- its scope to the table): an FFI declaration extends Σ; a monomorphic
-- definition is an arity-0 entry whose body is the term the checker's witness
-- names — the Spec's derivation of the body, read at the scope's Pack (the
-- table so far, each entry's name, whether it is inlined, and the View); a
-- telescope definition is an entry at its schema. The program runs a
-- reference to `main` (D253).
--
-- The Pack's names: an entry is named by its definition's name, a
-- monomorphic entry is called and a telescope entry inlined (`Names`).
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.ModuleProgram (Σ : Signature) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_<_; suc)
import Once.Spec.Core.Typing
import Once.Spec.Context
open import Once.Spec.Context using ([])
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using () renaming (_≟_ to _≟str_; _==_ to _==str_)
import Data.String.Properties as StrProp
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using () renaming (here to here′; there to there′)
import Once.Module
import Once.Spec.Core.Program
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Type using (Type)
import Once.Spec.Type as ST
import Once.Spec.Grade as LG
open import Once.Spec.Core.Syntax using (Defs; _▷_; _!!_; Schema)
import Once.Spec.Core.Syntax as SC
open import Once.Spec.Core.Program Σ using (Tele; def; Entry)
open import Once.Spec.Surface.Program using (_∷ⁿ_)
import Once.Spec.Surface.Typing as SUT
open import Once.Spec.Sub using (_<:_)
open import Once.Type.SubDecide using (_<:?_)
open import Once.Core.Telescope Σ using (Program)
open import Once.TypeCheck.Scope using (lookupImport; lookupPolyPrefix)
import Once.Type.Poly as TP
import Once.Compile as C
import Once.Parser as Parser
open import Once.Module using (Scope; ModTele; []; ffi; mono; poly; MainIn; EffUU; ctxOf; ctxOfAt; addImp; MonoWit; CheckRun)
import Once.TypeCheck.Scope
import Once.Surface.Syntax as SS
open import Once.TypeCheck.SpecWitness using (WC)
open import Once.Type.Instance using (kindsOf; rigidOf)
open import Once.Core.Translate Σ
  using (SigSig; ImpSig; TeleSig; []; s-ffi; i-def; t-def; wkI; wkT; impDefs; viewOf; impAt; telFind; monoSchema; u0;
         programAt; mainEntry; SigIn)
import Once.TypeCheck.View as TView
import Once.TypeCheck.Scoped as Sc
open import Once.TypeCheck.SpecWitness using (Pack)
import Once.TypeCheck.UseCore as UC
import Once.Adequacy.SpecFront.ScopeNames as SN
open import Once.Adequacy.SpecFront.SchemaOf using (ground-arity; open-arity; schema-arrow)
open import Once.Type.Schema using (schemaOf)

open Parser.FunInfo using (funName; funBody; funType)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)

------------------------------------------------------------------------
-- The names
------------------------------------------------------------------------

module _ {s} {S : Defs s} (inline : Fin s → Bool) where

  -- a monomorphic definition in scope is called…
  ImpCalled : ∀ {imps} → ImpSig S imps → Set
  ImpCalled []             = ⊤
  ImpCalled (i-def d e is) = (inline d ≡ false) × ImpCalled is

  -- …and a telescope definition inlined
  TeleInlined : ∀ {ps} → TeleSig S ps → Set
  TeleInlined []             = ⊤
  TeleInlined (t-def d e ts) = (inline d ≡ true) × TeleInlined ts

  h-call-of : ∀ {imps} (is : ImpSig S imps) → ImpCalled is → ∀ {x T} (lk : lookupImport imps x ≡ just T)
            → inline (TView.ImportAt.entryOf (impAt is lk)) ≡ false
  h-call-of [] _ ()
  h-call-of {(n , T₀) ∷ rest} (i-def d e is) (c , cs) {x} lk with StrProp._≟_ n x
  ... | yes _ with just-injective lk
  ...   | refl = c
  h-call-of {(n , T₀) ∷ rest} (i-def d e is) (c , cs) {x} lk | no _ = h-call-of is cs lk

  h-inline-of : ∀ {ps} (ts : TeleSig S ps) → TeleInlined ts → ∀ {x sc body prefix}
              → (lp : lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix))
              → inline (proj₁ (telFind ts lp)) ≡ true
  h-inline-of [] _ ()
  h-inline-of {p ∷ ps} (t-def d e ts) (i , is) {x} lp with StrProp._≟_ (pfunName p) x
  ... | yes _ with just-injective lp
  ...   | refl = i
  h-inline-of {p ∷ ps} (t-def d e ts) (i , is) {x} lp | no _ = h-inline-of ts is lp

-- The scope's names, at a table.
record Names {s} (S : Defs s) {imps ps} (is : ImpSig S imps) (ts : TeleSig S ps) : Set where
  field
    nm          : Fin s → CanonicalName
    inline      : Fin s → Bool
    imp-named   : SN.ImpNamed Σ S nm is
    imp-call    : ImpCalled inline is
    tele-named  : SN.TeleNamed Σ S nm ts
    tele-inline : TeleInlined inline ts
open Names

-- (the next entry's flag)
_∷ᵇ_ : ∀ {s} → Bool → (Fin s → Bool) → Fin (suc s) → Bool
(b ∷ᵇ f) zero    = b
(b ∷ᵇ f) (suc d) = f d

private
  imp-named-wk : ∀ {s} {S : Defs s} {sc′ c nm imps} (is : ImpSig S imps)
               → SN.ImpNamed Σ S nm is → SN.ImpNamed Σ (S ▷ sc′) (_∷ⁿ_ Σ c nm) (wkI is)
  imp-named-wk []             _         = tt
  imp-named-wk (i-def d e is) (nd , ns) = nd , imp-named-wk is ns

  tele-named-wk : ∀ {s} {S : Defs s} {sc′ c nm ps} (ts : TeleSig S ps)
                → SN.TeleNamed Σ S nm ts → SN.TeleNamed Σ (S ▷ sc′) (_∷ⁿ_ Σ c nm) (wkT ts)
  tele-named-wk []             _         = tt
  tele-named-wk (t-def d e ts) (nd , ns) = nd , tele-named-wk ts ns

  imp-call-wk : ∀ {s} {S : Defs s} {sc′ b inl imps} (is : ImpSig S imps)
              → ImpCalled inl is → ImpCalled {S = S ▷ sc′} (b ∷ᵇ inl) (wkI is)
  imp-call-wk []             _         = tt
  imp-call-wk (i-def d e is) (c , cs) = c , imp-call-wk is cs

  tele-inline-wk : ∀ {s} {S : Defs s} {sc′ b inl ps} (ts : TeleSig S ps)
                 → TeleInlined inl ts → TeleInlined {S = S ▷ sc′} (b ∷ᵇ inl) (wkT ts)
  tele-inline-wk []             _        = tt
  tele-inline-wk (t-def d e ts) (i , is) = i , tele-inline-wk ts is

-- No names, at the empty table.
names₀ : Names SC.[] [] []
names₀ = record { nm = λ () ; inline = λ () ; imp-named = tt ; imp-call = tt ; tele-named = tt ; tele-inline = tt }

-- A monomorphic definition: named, called; `main` (D324) joins the table only.
names-mono : ∀ {s} {S : Defs s} {imps ps} {is : ImpSig S imps} {ts : TeleSig S ps} (b : Bool) (x : _) (ty : Type)
           → Names S is ts → Names (S ▷ monoSchema ty) (impDefs b {x} {ty} is) (wkT ts)
names-mono {is = is} {ts} b x ty N = record
  { nm = _∷ⁿ_ Σ (canonical (x ∷ [])) (nm N) ; inline = false ∷ᵇ inline N
  ; imp-named = named b ; imp-call = called b
  ; tele-named = tele-named-wk ts (tele-named N) ; tele-inline = tele-inline-wk ts (tele-inline N) }
  where
    named : ∀ b → SN.ImpNamed Σ _ (_∷ⁿ_ Σ (canonical (x ∷ [])) (nm N)) (impDefs b {x} {ty} is)
    named true  = imp-named-wk is (imp-named N)
    named false = refl , imp-named-wk is (imp-named N)
    called : ∀ b → ImpCalled (false ∷ᵇ inline N) (impDefs b {x} {ty} is)
    called true  = imp-call-wk is (imp-call N)
    called false = refl , imp-call-wk is (imp-call N)

-- A telescope definition: named, inlined.
names-poly : ∀ {s} {S : Defs s} {imps ps} {is : ImpSig S imps} {ts : TeleSig S ps} (pfi : Parser.PolyFunInfo)
           → Names S is ts → Names (S ▷ schemaOf (pfunType pfi)) (wkI is) (t-def {p = pfi} zero refl (wkT ts))
names-poly {is = is} {ts} pfi N = record
  { nm = _∷ⁿ_ Σ (canonical (pfunName pfi ∷ [])) (nm N) ; inline = true ∷ᵇ inline N
  ; imp-named = imp-named-wk is (imp-named N) ; imp-call = imp-call-wk is (imp-call N)
  ; tele-named = refl , tele-named-wk ts (tele-named N) ; tele-inline = refl , tele-inline-wk ts (tele-inline N) }

------------------------------------------------------------------------
-- The Pack of a scope
------------------------------------------------------------------------

private
  arrow-at : ∀ {sc} (sch : Schema) → sch ≡ schemaOf sc → ∀ {sd sco π′} → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
           → Σ[ X ∈ ST.Ty (SC.Schema.arity sch) ] Σ[ Y ∈ ST.Ty (SC.Schema.arity sch) ]
               (SC.Schema.type sch ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y)
               × (∀ i → ST.Occurs i Y → ST.Occurs i X)
  arrow-at {sc} .(schemaOf sc) refl = schema-arrow sc

packOfAt : ∀ {m} (Δ : ST.KCtx m) {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
         → Names S is ts → Pack (ctxOfAt Δ sc)
packOfAt Δ {S = S} ss is ts N = record
  { Sg = Σ ; S = S ; nm = nm N ; inline = inline N ; V = viewOf {S = S} ss is ts
  ; h-imp = λ lk → proj₁ (SN.h-imp-of Σ S (nm N) is (imp-named N) lk)
  ; h-imp-call = h-call-of (inline N) is (imp-call N)
  ; h-poly = SN.h-poly-of Σ S (nm N) ts (tele-named N)
  ; h-poly-inline = h-inline-of (inline N) ts (tele-inline N)
  ; h-ground = λ {x} {sc} lp g → trans (cong SC.Schema.arity (proj₂ (telFind {S = S} ts lp))) (ground-arity sc g)
  ; h-open = λ {x} {sc} lp ng → subst (0 <_) (sym (cong SC.Schema.arity (proj₂ (telFind {S = S} ts lp)))) (open-arity sc ng)
  ; h-arrow = λ {x} {sc} lp → arrow-at {sc} _ (proj₂ (telFind {S = S} ts lp))
  ; L = SUT.∅
  ; lr = Sc.Locals.lo-∅ }

-- (a monomorphic definition's scope has no type variables)
packOf : ∀ {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
       → Names S is ts → Pack (ctxOf sc)
packOf = packOfAt ST.∅ₖ

------------------------------------------------------------------------
-- The entries
------------------------------------------------------------------------

-- A monomorphic definition's body: the term its witness names, at the scope's
-- Pack, typed in the core by the witness's usage.
monoBody : ∀ {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
         → (N : Names S is ts) → ∀ ft {e ty Ψ} → MonoWit ft (ctxOf sc) e ty Ψ
         → Σ[ t ∈ SC.Tm S 0 0 ] Once.Spec.Core.Typing._⊩_⊢[_]_∷_!_ Σ S ST.∅ₖ Once.Spec.Context.∅ [] t ty LG.pure
monoBody ss is ts N (just _) (_ , _ , _ , w , _) =
  let (t , u , _) = proj₂ w (packOf ss is ts N) in t , u0 (UC.typ⇐ Σ _ (nm N) _ _ ST.∅ₖ (proj₂ u))
monoBody ss is ts N nothing (_ , _ , _ , w , _) =
  let (t , u , _) = proj₂ w (packOf ss is ts N) in t , u0 (UC.typ⇒ Σ _ (nm N) _ _ ST.∅ₖ (proj₂ u))

-- …and the Spec's derivation of the body, naming that term.
monoCheck : ∀ {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
          → (N : Names S is ts) → ∀ {A e ty Ψ} (W : MonoWit (just A) (ctxOf sc) e ty Ψ)
          → SUT._⊢_⇐_↝_ Σ S (nm N) ST.∅ₖ SUT.∅ e ty (proj₁ (monoBody ss is ts N (just A) W))
monoCheck ss is ts N (_ , _ , _ , w , _) = proj₁ (proj₁ (proj₂ (proj₂ w (packOf ss is ts N))))

monoSynth : ∀ {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
          → (N : Names S is ts) → ∀ {e ty Ψ} (W : MonoWit nothing (ctxOf sc) e ty Ψ)
          → SUT._⊢_⇒_↝_ Σ S (nm N) ST.∅ₖ SUT.∅ e ty (proj₁ (monoBody ss is ts N nothing W))
monoSynth ss is ts N (_ , _ , _ , w , _) = proj₁ (proj₁ (proj₂ (proj₂ w (packOf ss is ts N))))

-- A telescope definition's witness: the checker's run of its body over its
-- parameters.
PolyWit : (sc : Scope) (pfi : Parser.PolyFunInfo) → Once.Spec.Context.Usage 0 → Set
PolyWit sc pfi Ψ = CheckRun (ctxOfAt (kindsOf (pfunType pfi)) sc) (pfunBody pfi) (rigidOf (pfunType pfi)) Ψ

-- Its body: the term its witness names, at the scope's Pack over the
-- parameters, typed in the core by the witness's usage.
polyBody : ∀ {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
         → (N : Names S is ts) → ∀ {pfi Ψ} → PolyWit sc pfi Ψ
         → Σ[ t ∈ SC.Tm S (SC.Schema.arity (schemaOf (pfunType pfi))) 0 ]
             Once.Spec.Core.Typing._⊩_⊢[_]_∷_!_ Σ S (kindsOf (pfunType pfi)) Once.Spec.Context.∅ [] t (rigidOf (pfunType pfi)) LG.pure
polyBody ss is ts N {pfi} (_ , _ , _ , w , _) =
  let (t , u , _) = proj₂ w (packOfAt (kindsOf (pfunType pfi)) ss is ts N)
  in t , u0 (UC.typ⇐ Σ _ (nm N) _ _ (kindsOf (pfunType pfi)) (proj₂ u))

-- …and the Spec's derivation of the body, naming that term.
polyCheck : ∀ {s} {S : Defs s} {sc : Scope} (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
          → (N : Names S is ts) → ∀ {pfi Ψ} (W : PolyWit sc pfi Ψ)
          → SUT._⊢_⇐_↝_ Σ S (nm N) (kindsOf (pfunType pfi)) SUT.∅ (pfunBody pfi) (rigidOf (pfunType pfi)) (proj₁ (polyBody ss is ts N {pfi} {Ψ} W))
polyCheck ss is ts N {pfi} (_ , _ , _ , w , _) = proj₁ (proj₁ (proj₂ (proj₂ w (packOfAt (kindsOf (pfunType pfi)) ss is ts N))))

-- A telescope definition: an entry at its schema, its body the witness's term.
polyDef : ∀ {s} {S : Defs s} {sc pfi Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
        → Names S is ts → PolyWit sc pfi Ψ → Tele (S ▷ schemaOf (pfunType pfi))
polyDef {pfi = pfi} {Ψ = Ψ} tl ss is ts N W =
  let (t , d) = polyBody ss is ts N {pfi} {Ψ} W in def tl (schemaOf (pfunType pfi)) t d

-- A monomorphic definition: an arity-0 entry, its body the witness's term.
monoDef : ∀ {s} {S : Defs s} {sc fi ty Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) (is : ImpSig S (Scope.imps sc)) (ts : TeleSig S (Scope.tele sc))
        → Names S is ts → MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ → Tele (S ▷ monoSchema ty)
monoDef {fi = fi} {ty = ty} tl ss is ts N W =
  let (t , d) = monoBody ss is ts N (funType fi) W in def tl (monoSchema ty) t d

------------------------------------------------------------------------
-- The program
------------------------------------------------------------------------

mutual
  toProgram : ∀ {s} {S : Defs s} {sc es} → Tele S → SigSig (Scope.sig sc) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
            → Names S is ts → (mt : ModTele sc es) → MainIn mt → SigIn mt → Program
  toProgram tl ss is ts N [] () u
  toProgram tl ss is ts N (ffi _ _ c h rest) mi u = toProgram tl (s-ffi c h (u (here′ refl)) ss) is ts N rest mi (λ m → u (there′ m))
  toProgram {S = S} {sc = sc} tl ss is ts N (poly {pfi = pfi} {Ψ = Ψ} pr W rest) mi u =
    toProgram (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W)
              ss (wkI is) (t-def zero refl (wkT ts)) (names-poly pfi N) rest mi u
  toProgram {S = S} {sc = sc} tl ss is ts N (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr W rest) mi u =
    monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi u

  monoPick : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
           → Names S is ts → (W : MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → ((funName fi ≡ "main") × (ty <: EffUU)) ⊎ MainIn rest
           → SigIn rest → Program
  monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest (inj₁ (_ , e)) u =
    monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest e u
  monoPick {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest (inj₂ mi′) u =
    monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ (funName fi ≟str "main") (ty <:? EffUU) u

  monoDispatch : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
               → Names S is ts → (W : MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
               → (rest : ModTele (addImp sc (funName fi) ty) es) → MainIn rest
               → Dec (funName fi ≡ "main") → Dec (ty <: EffUU) → SigIn rest → Program
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ (yes _) (yes e) u =
    monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest e u
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ (yes _) (no _) u =
    monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ u
  monoDispatch {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ (no _) _ u =
    monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ u

  monoNext : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
           → Names S is ts → (W : MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → MainIn rest → SigIn rest → Program
  monoNext {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest mi′ u =
    toProgram (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W)
              ss (impDefs (funName fi ==str "main") is) (wkT ts) (names-mono (funName fi ==str "main") (funName fi) ty N) rest mi′ u

  -- `main`: an entry like any other (D253); the program refers to it.
  monoHere : ∀ {s} {S : Defs s} {sc fi ty es Ψ} → Tele S → (ss : SigSig (Scope.sig sc)) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
           → Names S is ts → (W : MonoWit (funType fi) (ctxOf sc) (funBody fi) ty Ψ)
           → (rest : ModTele (addImp sc (funName fi) ty) es) → ty <: EffUU → SigIn rest → Program
  monoHere {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W rest e u =
    toProgramFrom (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W)
                  ss (impDefs (funName fi ==str "main") is) (wkT ts) (names-mono (funName fi ==str "main") (funName fi) ty N)
                  zero (mainEntry e) rest u

  -- The entries after `main`: the telescope goes on, `main`'s entry is weakened.
  toProgramFrom : ∀ {s} {S : Defs s} {sc es} → Tele S → SigSig (Scope.sig sc) → (is : ImpSig S (Scope.imps sc)) → (ts : TeleSig S (Scope.tele sc))
                → Names S is ts → (d : Fin s) → Entry (S !! d) → (mt : ModTele sc es) → SigIn mt → Program
  toProgramFrom tl ss is ts N d e [] u = programAt tl d e
  toProgramFrom tl ss is ts N d e (ffi _ _ c h rest) u = toProgramFrom tl (s-ffi c h (u (here′ refl)) ss) is ts N d e rest (λ m → u (there′ m))
  toProgramFrom {S = S} {sc = sc} tl ss is ts N d e (poly {pfi = pfi} {Ψ = Ψ} pr W rest) u =
    toProgramFrom (polyDef {S = S} {sc = sc} {pfi = pfi} {Ψ = Ψ} tl ss is ts N W)
                  ss (wkI is) (t-def zero refl (wkT ts)) (names-poly pfi N) (suc d) e rest u
  toProgramFrom {S = S} {sc = sc} tl ss is ts N d e (mono {fi = fi} {ty = ty} {Ψ = Ψ} ep er pr W rest) u =
    toProgramFrom (monoDef {S = S} {sc = sc} {fi = fi} {ty = ty} {Ψ = Ψ} tl ss is ts N W)
                  ss (impDefs (funName fi ==str "main") is) (wkT ts) (names-mono (funName fi ==str "main") (funName fi) ty N) (suc d) e rest u

-- A typed module's core program, over the signatures it is compiled against.
toProgram₀ : ∀ {es} (mt : ModTele Once.Module.emptyScope es) → MainIn mt → SigIn mt → Program
toProgram₀ mt mi u = toProgram {S = SC.[]} Once.Spec.Core.Program.Tele.[] [] [] [] names₀ mt mi u
