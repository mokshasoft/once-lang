-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.WalkMain — where the Spec's walk defines `main`
-- (plan 0.121 `complete`).
--
-- A program's walk names its definitions apart, and the one named `main` is
-- its entry (`Denotes.entry`, `Program.isMain`). So every step of the walk
-- that defines `main` defines an entry (`MainsW`, `walk-mains`), and some step
-- does (`MainW`, `walk-main`): each step's definition sits in the walk's end
-- (`walk-emb`). An entry's type is below `Eff Unit Unit`, so a written one is
-- a concrete ground type (`entry-concrete`): the compiler reads it as a
-- monomorphic definition.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)

module Once.Adequacy.SpecFront.WalkMain (Σ : Signature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Spec.Name using (CanonicalName; canonical)
import Once.Spec.Type as ST
import Once.Spec.Sub as SS
import Once.Spec.Core.Syntax as SC
open SC.Schema using (arity; kinds; type)
import Once.Spec.Surface.Program as SPr
open import Once.Spec.Core.Program Σ using (Entry; entry; EffUU)
open import Once.Adequacy.SpecFront.GuardBack using (defNamesS)

------------------------------------------------------------------------
-- The steps that define `main`
------------------------------------------------------------------------

module _ where
  open SPr using (Walk; w-end; w-skip; w-sig; w-nosig)

  -- every step defining `main` defines an entry…
  MainsW : ∀ {s} {S : SC.Defs s} {nm tl ds s″} {S″ : SC.Defs s″} {nm″ tl″} → Walk Σ S nm tl ds S″ nm″ tl″ → Set
  MainsW w-end                                   = ⊤
  MainsW (w-skip _ w)                            = MainsW w
  MainsW (w-sig {x = x} {sc = sc} _ _ _ w)       = (x ≡ "main" → Entry sc) × MainsW w
  MainsW (w-nosig {x = x} {A = A} _ _ _ w)       = (x ≡ "main" → A SS.<: EffUU) × MainsW w

  -- …and some step does
  MainW : ∀ {s} {S : SC.Defs s} {nm tl ds s″} {S″ : SC.Defs s″} {nm″ tl″} → Walk Σ S nm tl ds S″ nm″ tl″ → Set
  MainW w-end                                    = ⊥
  MainW (w-skip _ w)                             = MainW w
  MainW (w-sig {x = x} {sc = sc} _ _ _ w)        = ((x ≡ "main") × Entry sc) ⊎ MainW w
  MainW (w-nosig {x = x} {A = A} _ _ _ w)        = ((x ≡ "main") × (A SS.<: EffUU)) ⊎ MainW w

  -- The walk's start sits in its end.
  walk-emb : ∀ {s} {S : SC.Defs s} {nm tl ds s″} {S″ : SC.Defs s″} {nm″ tl″} → Walk Σ S nm tl ds S″ nm″ tl″
           → Σ[ ι ∈ (Fin s → Fin s″) ] (∀ d → (nm″ (ι d) ≡ nm d) × (S″ SC.!! ι d ≡ S SC.!! d))
  walk-emb w-end           = (λ d → d) , λ d → refl , refl
  walk-emb (w-skip _ w)    = walk-emb w
  walk-emb (w-sig _ _ _ w) = let (ι , h) = walk-emb w in (λ d → ι (suc d)) , λ d → h (suc d)
  walk-emb (w-nosig _ _ _ w) = let (ι , h) = walk-emb w in (λ d → ι (suc d)) , λ d → h (suc d)

  private
    -- the newest definition of a step, in the walk's end
    newest : ∀ {s} {S : SC.Defs s} {nm x sc tl ds s″} {S″ : SC.Defs s″} {nm″ tl″}
           → Walk Σ (S SC.▷ sc) (SPr._∷ⁿ_ Σ (canonical (x ∷ [])) nm) tl ds S″ nm″ tl″
           → Σ[ i ∈ Fin s″ ] (nm″ i ≡ canonical (x ∷ [])) × (S″ SC.!! i ≡ sc)
    newest w = let (ι , h) = walk-emb w in ι zero , h zero

    entry-at : ∀ {sc sc′} → sc ≡ sc′ → Entry sc → Entry sc′
    entry-at refl e = e

    entry-type : ∀ {k : ST.KCtx 0} {A} → Entry (SC.schema 0 k A) → A SS.<: EffUU
    entry-type (entry p) = p

  -- Where the end's `main` is an entry, so is every step's `main`.
  walk-mains : ∀ {s} {S : SC.Defs s} {nm tl ds s″} {S″ : SC.Defs s″} {nm″ tl″} (w : Walk Σ S nm tl ds S″ nm″ tl″)
             → (∀ i → nm″ i ≡ canonical ("main" ∷ []) → Entry (S″ SC.!! i)) → MainsW w
  walk-mains w-end h = tt
  walk-mains (w-skip _ w) h = walk-mains w h
  walk-mains (w-sig _ _ _ w) h =
    (λ { refl → let (i , ni , si) = newest w in entry-at si (h i ni) }) , walk-mains w h
  walk-mains (w-nosig _ _ _ w) h =
    (λ { refl → let (i , ni , si) = newest w in entry-type (entry-at si (h i ni)) }) , walk-mains w h

  -- A walk that defines `main` has a step that does.
  walk-main : ∀ {s} {S : SC.Defs s} {nm tl ds s″} {S″ : SC.Defs s″} {nm″ tl″} (w : Walk Σ S nm tl ds S″ nm″ tl″)
            → "main" ∈ defNamesS ds → (∀ i → nm″ i ≡ canonical ("main" ∷ []) → Entry (S″ SC.!! i)) → MainW w
  walk-main w-end () h
  walk-main (w-skip SPr.nd-sig w)    m h = walk-main w m h
  walk-main (w-skip SPr.nd-alias w)  m h = walk-main w m h
  walk-main (w-skip SPr.nd-import w) m h = walk-main w m h
  walk-main (w-sig {x = x} {ds = ds} {sc = sc} _ _ _ w) m h = at (x ≟ "main") m
    where
      at : Dec (x ≡ "main") → "main" ∈ x ∷ defNamesS ds → ((x ≡ "main") × Entry sc) ⊎ MainW w
      at (yes refl) _         = let (i , ni , si) = newest w in inj₁ (refl , entry-at si (h i ni))
      at (no ne)    (here e)  = ⊥-elim (ne (sym e))
      at (no ne)    (there m′) = inj₂ (walk-main w m′ h)
  walk-main (w-nosig {x = x} {ds = ds} {A = A} _ _ _ w) m h = at (x ≟ "main") m
    where
      at : Dec (x ≡ "main") → "main" ∈ x ∷ defNamesS ds → ((x ≡ "main") × (A SS.<: EffUU)) ⊎ MainW w
      at (yes refl) _         = let (i , ni , si) = newest w in inj₁ (refl , entry-type (entry-at si (h i ni)))
      at (no ne)    (here e)  = ⊥-elim (ne (sym e))
      at (no ne)    (there m′) = inj₂ (walk-main w m′ h)

------------------------------------------------------------------------
-- An entry's written type is a concrete ground type
------------------------------------------------------------------------

open import Once.Spec.Surface.Syntax as LP using (PolyType; PolyFunctor)
open import Once.Internal.Type.Poly as LP using (Ground; GroundF; extractGround)
import Once.Internal.Type as LT
import Once.Spec.Type as LT
import Once.Spec.Grade as LG
open import Once.Internal.Type.WellFormed using (IsConcrete; IsBaseType; con-base; con-fun; base-Unit; base-Void)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly; toPolyF)
open SPr using (TypeOf; FunOf; SchemaOf; to-var; to-unit; to-void; to-int; to-float; to-*; to-+; to-⇒; to-act; to-eff; to-μ; to-ν;
                fo-K; fo-Id; fo-⊕; fo-⊗)

private
  mutual
    -- read without variables, it is ground
    g0 : ∀ (T : PolyType) {ns : Fin 0 → String} {A} → TypeOf ns (toPoly T) A → Ground T
    g0 LP.PUnit           to-unit      = tt
    g0 LP.PVoid           to-void      = tt
    g0 LP.PInt            to-int       = tt
    g0 LP.PFloat          to-float     = tt
    g0 (A LP.P* B)        (to-* a b)   = g0 A a , g0 B b
    g0 (A LP.P+ B)        (to-+ a b)   = g0 A a , g0 B b
    g0 (A LP.P⇒[ q ] B)   (to-⇒ a b)   = g0 A a , g0 B b
    g0 (LP.PEff A B)      (to-eff a b) = g0 A a , g0 B b
    g0 (LP.PAct A B)      (to-act a b) = g0 A a , g0 B b
    g0 (LP.Pμ F)     (to-μ f)     = g0F F f
    g0 (LP.Pν F φ)   (to-ν f)     = g0F F f
    g0 (LP.PTVar x)       (to-var () _)

    g0F : ∀ (F : PolyFunctor) {ns : Fin 0 → String} {G} → FunOf ns (toPolyF F) G → GroundF F
    g0F (LP.PK A)     (fo-K a)   = g0 A a
    g0F LP.PId        fo-Id      = tt
    g0F (F LP.P⊕ G)   (fo-⊕ f g) = g0F F f , g0F G g
    g0F (F LP.P⊗ G)   (fo-⊗ f g) = g0F F f , g0F G g

  -- a domain above `Unit` is `Unit`
  dom-base : ∀ (T : PolyType) {ns : Fin 0 → String} {X} (r : TypeOf ns (toPoly T) X) → ST.Unit SS.<: X
           → IsBaseType (extractGround T (g0 T r))
  dom-base LP.PUnit to-unit SS.sub-unit = base-Unit
  dom-base LP.PVoid to-void ()
  dom-base LP.PInt to-int ()
  dom-base LP.PFloat to-float ()
  dom-base (A LP.P* B) (to-* a b) ()
  dom-base (A LP.P+ B) (to-+ a b) ()
  dom-base (A LP.P⇒[ q ] B) (to-⇒ a b) ()
  dom-base (LP.PEff A B) (to-eff a b) ()
  dom-base (LP.PAct A B) (to-act a b) ()
  dom-base (LP.Pμ F) (to-μ f) ()
  dom-base (LP.Pν F φ) (to-ν f) ()
  dom-base (LP.PTVar x) (to-var () _)

  -- a codomain below `Unit` is `Unit` or `Void`
  cod-base : ∀ (T : PolyType) {ns : Fin 0 → String} {X} (r : TypeOf ns (toPoly T) X) → X SS.<: ST.Unit
           → IsBaseType (extractGround T (g0 T r))
  cod-base LP.PUnit to-unit SS.sub-unit = base-Unit
  cod-base LP.PVoid to-void SS.sub-void = base-Void
  cod-base LP.PInt to-int ()
  cod-base LP.PFloat to-float ()
  cod-base (A LP.P* B) (to-* a b) ()
  cod-base (A LP.P+ B) (to-+ a b) ()
  cod-base (A LP.P⇒[ q ] B) (to-⇒ a b) ()
  cod-base (LP.PEff A B) (to-eff a b) ()
  cod-base (LP.PAct A B) (to-act a b) ()
  cod-base (LP.Pμ F) (to-μ f) ()
  cod-base (LP.Pν F φ) (to-ν f) ()
  cod-base (LP.PTVar x) (to-var () _)

  conc : ∀ (T : PolyType) {ns : Fin 0 → String} {A} (r : TypeOf ns (toPoly T) A) → A SS.<: EffUU
       → IsConcrete (extractGround T (g0 T r))
  conc LP.PVoid to-void SS.sub-void = con-base base-Void
  conc LP.PUnit to-unit ()
  conc LP.PInt to-int ()
  conc LP.PFloat to-float ()
  conc (A LP.P* B) (to-* a b) ()
  conc (A LP.P+ B) (to-+ a b) ()
  conc (A LP.P⇒[ LG.Many ] B) (to-⇒ a b) (SS.sub-arr d c _) = con-fun (dom-base A a d) (cod-base B b c)
  conc (A LP.P⇒[ LG.One ] B) (to-⇒ a b) ()
  conc (A LP.P⇒[ LG.Zero ] B) (to-⇒ a b) ()
  conc (LP.PEff A B) (to-eff a b) (SS.sub-arr d c _) = con-fun (dom-base A a d) (cod-base B b c)
  conc (LP.PAct A B) (to-act a b) (SS.sub-arr d c _) = con-fun (dom-base A a d) (cod-base B b c)
  conc (LP.Pμ F) (to-μ f) ()
  conc (LP.Pν F φ) (to-ν f) ()
  conc (LP.PTVar x) (to-var () _)

-- A written type the Spec reads as an entry is a concrete ground type.
entry-concrete : ∀ (T : PolyType) {sc} → SchemaOf (toPoly T) sc → Entry sc → Σ[ g ∈ Ground T ] IsConcrete (extractGround T g)
entry-concrete T so (entry p) = g0 T (SchemaOf.reads so) , conc T (SchemaOf.reads so) p
