-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Inst — a Spec instance of a telescope entry is a
-- compiler instance of its schema (plan 0.121 §3.6, F6).
--
-- A Spec reference to a polymorphic definition is at an instance `τ` of the
-- definition's schema, respecting its kinds; the compiler's at a kinded
-- instance of the schema as written (`KindedInstance sc`). A compiler type
-- related to the Spec instance IS a kinded instance: each variable at the
-- compiler type read back from its Spec instance (`back`), which is the one
-- the type has there, since a Spec type relates one compiler type
-- (`inst-eq`). With this: what F5 asks of a telescope entry (`Scope.PolyAt`)
-- apart from where the scope finds it — its instances (`inst-at`), a ground
-- schema at its one type (`ground-at`), an open one (`open-at`), and an
-- arrow schema (`arrow-at`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Once.Spec.Type as ST

module Once.Adequacy.SpecFront.Inst {m : ℕ} (Δ : ST.KCtx m) where

open import Data.Nat using (_<_; s≤s; z≤n)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
import Data.String
import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.DecPropositional Data.String._≟_ using (_∈?_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

import Once.Spec.Type as LT
import Once.Spec.Grade as LG
open import Once.Spec.Grade using (mk-kind; Many; pure; act; eff)
import Once.Internal.Type.WellFormed as LW
import Once.Spec.Type as LW
import Once.Internal.Type.Poly as TP
open import Once.Spec.Surface.Syntax using (PolyType; PolyFunctor; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ; Pν; PK; PId; _P⊕_; _P⊗_)
open import Once.Internal.Type.Poly using (substPoly; substPolyF; ftv; ftvF; Ground; extractGround; ArrowSchema; as-pure; as-eff; as-act; CodVarsInDom)
open import Once.Internal.Type.Instance using (params; nubFrom; arityOf; ftvK; KindedInstance; RespectsKinds)
open import Once.Internal.Type.Schema using (schemaOf)
import Once.Spec.Grade as SG
import Once.Spec.Core.Syntax as SC
open import Once.Type.Rigid using (subst-ground; ftvK⊆ftv)
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS; schS; kindsS)
open import Once.Adequacy.SpecFront.Types Δ using (back)
open import Once.Adequacy.SpecFront.SchemaOf using (module Parts; ground-arity; schemaOf-S; empty-ground)
open import Once.Spec.Surface.Program using (SchemaOf)

module _ (T : PolyType) where

  open Parts T

  -- each variable at the compiler type its instance reads back as
  θ-at : ST.TySub (arityOf T) m → (x : String) → Dec (x ∈ ftv T) → ST.Ty m
  θ-at τ x (yes mm) = proj₁ (back (τ (j mm)))
  θ-at τ x (no _)   = LT.Unit

  θ : ST.TySub (arityOf T) m → String → ST.Ty m
  θ τ x = θ-at τ x (x ∈? ftv T)

  θ-is : ∀ τ {x} (mm : x ∈ ftv T) (d : Dec (x ∈ ftv T)) → θ-at τ x d ≡ proj₁ (back (τ (j mm)))
  θ-is τ mm (yes mm′) = cong (λ k → proj₁ (back (τ k))) (j-irr mm′ mm)
  θ-is τ mm (no ¬mm)  = ⊥-elim (¬mm mm)

  θ-R : ∀ τ {x} (mm : x ∈ ftv T) → TyR Δ (θ τ x) (τ (j mm))
  θ-R τ {x} mm = subst (λ U → TyR Δ U (τ (j mm))) (sym (θ-is τ mm (x ∈? ftv T))) (proj₂ (back (τ (j mm))))

  private
    ˡ : ∀ {A B : List String} {x} → (∀ {y} → y ∈ A Data.List.++ B → y ∈ ftv T) → x ∈ A → x ∈ ftv T
    ˡ s mm = s (Data.List.Membership.Propositional.Properties.∈-++⁺ˡ mm)
    ʳ : ∀ (A : List String) {B : List String} {x} → (∀ {y} → y ∈ A Data.List.++ B → y ∈ ftv T) → x ∈ B → x ∈ ftv T
    ʳ A s mm = s (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ A mm)

    arr : ∀ {A B A′ B′ : ST.Ty m} {k k′} → A ≡ A′ → k ≡ k′ → B ≡ B′ → (A LT.⇒[ k ] B) ≡ (A′ LT.⇒[ k′ ] B′)
    arr refl refl refl = refl

    νeq : ∀ {F F′ : ST.Fun m} {φ φ′} → F ≡ F′ → φ ≡ φ′ → LT.ν F φ ≡ LT.ν F′ φ′
    νeq refl refl = refl

  -- A compiler type related to the part at `τ` is the part at `θ τ`.
  mutual
    inst-eq : ∀ τ A (s : ∀ {x} → x ∈ ftv A → x ∈ ftv T) {U} → TyR Δ U (ptyS (ab A) ST.⟨ τ ⟩) → substPoly (θ τ) A ≡ U
    inst-eq τ (PTVar x) s r =
      TyR-uniqueˡ (θ-R τ (s (here refl))) (subst (TyR Δ _) (cong (ST._⟨ τ ⟩) (var-ab (s (here refl)))) r)
    inst-eq τ PUnit  s r-unit  = refl
    inst-eq τ PVoid  s r-void  = refl
    inst-eq τ PInt   s r-int   = refl
    inst-eq τ PFloat s r-float = refl
    inst-eq τ (A P* B) s (r-* a b) = cong₂ LT._*_ (inst-eq τ A (ˡ s) a) (inst-eq τ B (ʳ (ftv A) s) b)
    inst-eq τ (A P+ B) s (r-+ a b) = cong₂ LT._+_ (inst-eq τ A (ˡ s) a) (inst-eq τ B (ʳ (ftv A) s) b)
    inst-eq τ (A P⇒[ q ] B) s (r-⇒ e a b) = arr (inst-eq τ A (ˡ s) a) (sym (kS-injective e)) (inst-eq τ B (ʳ (ftv A) s) b)
    inst-eq τ (PEff A B)    s (r-⇒ e a b) = arr (inst-eq τ A (ˡ s) a) (sym (kS-injective e)) (inst-eq τ B (ʳ (ftv A) s) b)
    inst-eq τ (PAct A B)    s (r-⇒ e a b) = arr (inst-eq τ A (ˡ s) a) (sym (kS-injective e)) (inst-eq τ B (ʳ (ftv A) s) b)
    inst-eq τ (Pμ F)   s (r-μ f)     = cong LT.μ (instF-eq τ F s f)
    inst-eq τ (Pν F φ) s (r-ν e f)   = νeq (instF-eq τ F s f) (sym (φS-injective e))

    instF-eq : ∀ τ F (s : ∀ {x} → x ∈ ftvF F → x ∈ ftv T) {G} → FunR Δ G (pfunS (abF F) ST.⟨ τ ⟩F) → substPolyF (θ τ) F ≡ G
    instF-eq τ (PK A)   s (r-K a)   = cong LT.K (inst-eq τ A s a)
    instF-eq τ PId      s r-Id      = refl
    instF-eq τ (F P⊕ G) s (r-⊕ f g) = cong₂ LT._⊕_ (instF-eq τ F (ˡ s) f) (instF-eq τ G (ʳ (ftvF F) s) g)
    instF-eq τ (F P⊗ G) s (r-⊗ f g) = cong₂ LT._⊗_ (instF-eq τ F (ˡ s) f) (instF-eq τ G (ʳ (ftvF F) s) g)

  -- An instance respecting the kinds reads back to one respecting them.
  respects : ∀ τ → ST.Respects (kindsS κ) Δ τ → RespectsKinds Δ T (θ τ)
  respects τ rs {x} mk =
    let mm = ftvK⊆ftv T mk
        u  = SchemaOf.kinded (schemaOf-S T) (j mm)
        e  = proj₁ u (Parts.underK T T (λ m′ → m′) (j mm) (subst (_∈ ftvK T) (sym (name-j mm)) mk))
    in base-L (rs (j mm) e) (θ-R τ mm)

------------------------------------------------------------------------
-- An entry's schema
------------------------------------------------------------------------

-- Its instances.
inst-at : ∀ (sc : PolyType) (sch : SC.Schema) → sch ≡ schS (schemaOf sc)
        → ∀ (τ : ST.TySub (SC.Schema.arity sch) m) → ST.Respects (SC.Schema.kinds sch) Δ τ
        → ∀ {U} → TyR Δ U (SC.Schema.type sch ST.⟨ τ ⟩) → KindedInstance Δ sc U
inst-at sc .(schS (schemaOf sc)) refl τ rs r = θ sc τ , inst-eq sc τ sc (λ m′ → m′) r , respects sc τ rs

-- No type variables: ground, at its one type.
private
  nub-nonempty : ∀ {x xs} → 0 < length (nubFrom [] (x ∷ xs))
  nub-nonempty = s≤s z≤n

  arity0-ftv : ∀ sc → arityOf sc ≡ 0 → ftv sc ≡ []
  arity0-ftv sc e = go (ftv sc) refl
    where
      go : ∀ l → ftv sc ≡ l → ftv sc ≡ []
      go []      el = el
      go (x ∷ l) el = ⊥-elim (lt0 (subst (λ n → 0 < n) e (subst (λ l′ → 0 < length (nubFrom [] l′)) (sym el) (nub-nonempty {x} {l}))))
        where
          lt0 : 0 < 0 → ⊥
          lt0 ()

ground-at : ∀ (sc : PolyType) (sch : SC.Schema) → sch ≡ schS (schemaOf sc) → SC.Schema.arity sch ≡ 0
          → Σ[ g ∈ Ground sc ] (∀ τ → TyR Δ (extractGround sc g) (SC.Schema.type sch ST.⟨ τ ⟩))
ground-at sc .(schS (schemaOf sc)) refl ar =
  g , λ τ → let (U , r) = back (ptyS (Parts.ab sc sc) ST.⟨ τ ⟩)
            in subst (λ U′ → TyR Δ U′ _) (trans (sym (inst-eq sc τ sc (λ m′ → m′) r)) (subst-ground (θ sc τ) sc g)) r
  where
    g : Ground sc
    g = empty-ground sc (arity0-ftv sc ar)

-- Type variables: not ground.
open-at : ∀ (sc : PolyType) (sch : SC.Schema) → sch ≡ schS (schemaOf sc) → 0 < SC.Schema.arity sch → ¬ Ground sc
open-at sc .(schS (schemaOf sc)) refl pos g = lt0 (subst (λ n → 0 < n) (ground-arity sc g) pos)
  where
    lt0 : 0 < 0 → ⊥
    lt0 ()

-- An arrow: the schema is an arrow schema, its codomain's variables in its
-- domain.
private
  no-arr : ∀ {a} {j : Fin a} {X Y : ST.Ty a} {k} → ST.var j ≡ X ST.⇒[ k ] Y → ⊥
  no-arr ()

  -- (the arrow's halves are the schema's parts)
  cod-in : ∀ sc A B → (∀ {x} → x ∈ ftv A Data.List.++ ftv B → x ∈ ftv sc)
         → ∀ {sd sco : ST.Ty (arityOf sc)} {k} → ptyS (Parts.ab sc A) ST.⇒[ k ] ptyS (Parts.ab sc B) ≡ sd ST.⇒[ k ] sco
         → (∀ i → ST.Occurs i sco → ST.Occurs i sd) → CodVarsInDom A B
  cod-in sc A B s refl incl {x} mB =
    let sA = λ {y} (m′ : y ∈ ftv A) → s (Data.List.Membership.Propositional.Properties.∈-++⁺ˡ m′)
        sB = λ {y} (m′ : y ∈ ftv B) → s (Data.List.Membership.Propositional.Properties.∈-++⁺ʳ (ftv A) m′)
        o  = incl _ (Parts.occ sc B sB mB)
    in subst (_∈ ftv A) (Parts.name-j sc (sB mB)) (Parts.occ⁻ sc A sA o)

  arrow-go : ∀ (sc : PolyType) {sd sco : ST.Ty (arityOf sc)} {π′}
           → ptyS (Parts.ab sc sc) ≡ sd ST.⇒[ SG.mk-kind SG.Many π′ ] sco
           → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
           → ∀ π → πS π ≡ π′ → Σ[ sd₀ ∈ PolyType ] Σ[ sc₀ ∈ PolyType ] ArrowSchema sc sd₀ sc₀ π × CodVarsInDom sd₀ sc₀
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

arrow-at : ∀ (sc : PolyType) (sch : SC.Schema) → sch ≡ schS (schemaOf sc)
         → ∀ {sd sco π′} → SC.Schema.type sch ≡ sd ST.⇒[ SG.mk-kind SG.Many π′ ] sco
         → (∀ i → ST.Occurs i sco → ST.Occurs i sd)
         → ∀ π → πS π ≡ π′ → Σ[ sd₀ ∈ PolyType ] Σ[ sc₀ ∈ PolyType ] ArrowSchema sc sd₀ sc₀ π × CodVarsInDom sd₀ sc₀
arrow-at sc .(schS (schemaOf sc)) refl e incl π pe = arrow-go sc e incl π pe
