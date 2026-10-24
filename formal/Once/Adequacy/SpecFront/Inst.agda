-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Inst — a telescope entry's arrow schema (plan
-- 0.121 §3.6, F6).
--
-- An entry whose type is an arrow whose codomain's variables occur in its
-- domain has, as written, an arrow schema with that property (`arrow-at`):
-- what the checker's domain-given rule for a telescope head reads.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Inst where

open import Data.Fin using (Fin)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.List
import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

import Once.Spec.Type as ST
import Once.Spec.Grade as LG
open import Once.Spec.Grade using (Many; pure; act; eff)
open import Once.Spec.Surface.Syntax using (PolyType; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν)
open import Once.Internal.Type.Poly using (ftv; ArrowSchema; as-pure; as-eff; as-act; CodVarsInDom)
open import Once.Internal.Type.Instance using (arityOf)
open import Once.Internal.Type.Schema using (schemaOf)
import Once.Spec.Grade as SG
import Once.Spec.Core.Syntax as SC
open import Once.Adequacy.SpecFront.SchemaOf using (module Parts)

-- An arrow: the schema is an arrow schema, its codomain's variables in its
-- domain.
private
  no-arr : ∀ {a} {j : Fin a} {X Y : ST.Ty a} {k} → ST.var j ≡ X ST.⇒[ k ] Y → ⊥
  no-arr ()

  -- (the arrow's halves are the schema's parts)
  cod-in : ∀ sc A B → (∀ {x} → x ∈ ftv A Data.List.++ ftv B → x ∈ ftv sc)
         → ∀ {sd sco : ST.Ty (arityOf sc)} {k} → (Parts.ab sc A) ST.⇒[ k ] (Parts.ab sc B) ≡ sd ST.⇒[ k ] sco
         → (∀ i → ST.Occurs i sco → ST.Occurs i sd) → CodVarsInDom A B
  cod-in sc A B s refl incl {x} mB =
    let sA = λ {y} (m′ : y ∈ ftv A) → s (Data.List.Membership.Propositional.Properties.∈-++⁺ˡ m′)
        sB = λ {y} (m′ : y ∈ ftv B) → s (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ (ftv A) m′)
        o  = incl _ (Parts.occ sc B sB mB)
    in subst (_∈ ftv A) (Parts.name-j sc (sB mB)) (Parts.occ⁻ sc A sA o)

  arrow-go : ∀ (sc : PolyType) {sd sco : ST.Ty (arityOf sc)} {π′}
           → (Parts.ab sc sc) ≡ sd ST.⇒[ SG.mk-kind SG.Many π′ ] sco
           → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
           → ∀ π → π ≡ π′ → Σ[ sd₀ ∈ PolyType ] Σ[ sc₀ ∈ PolyType ] ArrowSchema sc sd₀ sc₀ π × CodVarsInDom sd₀ sc₀
  arrow-go (PTVar x) e _ _ _ = ⊥-elim (no-arr (trans (sym (Parts.var-ab (PTVar x) (here refl))) e))
  arrow-go PUnit  () _ _ _
  arrow-go PVoid  () _ _ _
  arrow-go PInt   () _ _ _
  arrow-go PFloat () _ _ _
  arrow-go (A P* B) () _ _ _
  arrow-go (A P+ B) () _ _ _
  arrow-go (Pμ F) () _ _ _
  arrow-go (Pν F φ) () _ _ _
  arrow-go (A P⇒[ Many ] B) refl incl pure _ = A , B , as-pure , cod-in (A P⇒[ Many ] B) A B (λ m′ → m′) {k = SG.mk-kind SG.Many SG.pure} refl incl
  arrow-go (A P⇒[ Many ] B) refl incl act ()
  arrow-go (A P⇒[ Many ] B) refl incl eff ()
  arrow-go (A P⇒[ LG.Zero ] B) () _ _ _
  arrow-go (A P⇒[ LG.One ] B) () _ _ _
  arrow-go (PEff A B) refl incl eff _ = A , B , as-eff , cod-in (PEff A B) A B (λ m′ → m′) {k = SG.mk-kind SG.Many SG.eff} refl incl
  arrow-go (PEff A B) refl incl pure ()
  arrow-go (PEff A B) refl incl act ()
  arrow-go (PAct A B) refl incl act _ = A , B , as-act , cod-in (PAct A B) A B (λ m′ → m′) {k = SG.mk-kind SG.Many SG.act} refl incl
  arrow-go (PAct A B) refl incl pure ()
  arrow-go (PAct A B) refl incl eff ()

arrow-at : ∀ (sc : PolyType) (sch : SC.Schema) → sch ≡ (schemaOf sc)
         → ∀ {sd sco π′} → SC.Schema.type sch ≡ sd ST.⇒[ SG.mk-kind SG.Many π′ ] sco
         → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
         → ∀ π → π ≡ π′ → Σ[ sd₀ ∈ PolyType ] Σ[ sc₀ ∈ PolyType ] ArrowSchema sc sd₀ sc₀ π × CodVarsInDom sd₀ sc₀
arrow-at sc .((schemaOf sc)) refl e incl π pe = arrow-go sc e incl π pe
