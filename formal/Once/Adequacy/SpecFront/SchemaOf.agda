-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.SchemaOf — the compiler's schema of a written type
-- is the Spec's (plan 0.121 §3.6, F6).
--
-- The compiler reads a signature's type `T` as the schema `schemaOf T`: its
-- parameters are `T`'s variables in order of first occurrence (`params`),
-- each of base kind exactly when it occurs under a functor constant, and its
-- type is `T` at the rigid constants, abstracted. The Spec reads the written
-- type as a schema too (`SchemaOf`: distinct names, each used, the type read
-- through them, kinds by `UnderK`). They agree (`schemaOf-S`).
--
-- On the way: a parameter's index is its position (`params` has no
-- repetition), every parameter occurs in the type, and a variable of a part
-- of the type occurs exactly when it is one of the part's (`occ`/`occ⁻`).
-- The facts the front-end bridge asks of a telescope entry follow
-- (`ground-arity`, `open-arity`, `entry-occ`, `entry-arrow`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.SchemaOf where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective)
open import Data.List using (List; []; _∷_; _++_; length; lookup)
open import Data.List.Properties using (++-conicalˡ; ++-conicalʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Function using (Injective)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

import Once.Internal.Type as LT
open import Once.Spec.Grade using (mk-kind; Many; pure; act; eff)
import Once.Internal.Type.Poly as TP
open TP using (PolyType; PolyFunctor; PTVar; PUnit; PVoid; PInt; PFloat; _P*_; _P+_; _P⇒[_]_; PEff; PAct; Pμ-type; Pν-type;
               PK; PId; _P⊕_; _P⊗_; substPoly; substPolyF; ftv; ftvF; Ground; GroundF; ArrowSchema; as-pure; as-eff; as-act; CodVarsInDom)
open import Once.Internal.Type.Instance using (params; nubFrom; arityOf; kindOf; kindsOf; positionOf; memberB; rigidSubst; rigidOf; ftvK; ftvKF)
open import Once.Internal.Type.Schema using (schemaOf; ∈-params; positionOf-∈; memberB-sound; memberB-complete; lookup-∈)
import Once.Spec.Core.Syntax as SC
open import Data.Maybe using (Maybe; just; nothing; maybe′)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
import Once.Spec.Type as ST
open ST using (Occurs; OccursF; o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ˡ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ)
import Once.Spec.Surface.Syntax as SS
open import Once.Spec.Surface.Program
  using (TypeOf; FunOf; SchemaOf; UnderK; UnderKF;
         to-var; to-unit; to-void; to-int; to-float; to-*; to-+; to-⇒; to-act; to-eff; to-μ; to-ν; fo-K; fo-Id; fo-⊕; fo-⊗;
         uk-*ˡ; uk-*ʳ; uk-+ˡ; uk-+ʳ; uk-⇒ˡ; uk-⇒ʳ; uk-μ; uk-ν; uk-K; uk-⊕ˡ; uk-⊕ʳ; uk-⊗ˡ; uk-⊗ʳ)
open import Once.Type.Rigid using (ftv-ground)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly; toPolyF)
open import Once.Adequacy.SpecCore.Schema using (ptyS; pfunS; schS; kindsS)

------------------------------------------------------------------------
-- The parameters: no repetition, all of the type's variables
------------------------------------------------------------------------

private
  member-false : ∀ {y x seen} → memberB y (x ∷ seen) ≡ false → memberB y seen ≡ false
  member-false {y} {x} {seen} e = go (memberB y seen) refl
    where
      go : ∀ b → memberB y seen ≡ b → b ≡ false
      go false _  = refl
      go true  e′ = ⊥-elim (true≢false (trans (sym (memberB-complete y (x ∷ seen) (there (memberB-sound y seen e′)))) e))
        where
          true≢false : true ≡ false → ⊥
          true≢false ()

  member-ne : ∀ {y x seen} → memberB y (x ∷ seen) ≡ false → y ≢ x
  member-ne {y} {x} {seen} e refl = t≢f (trans (sym (memberB-complete y (y ∷ seen) (here refl))) e)
    where
      t≢f : true ≡ false → ⊥
      t≢f ()

nub-⊆ : ∀ seen xs {y} → y ∈ nubFrom seen xs → y ∈ xs
nub-⊆ seen []       ()
nub-⊆ seen (x ∷ xs) {y} m = go (memberB x seen) m
  where
    go : ∀ b → y ∈ (if b then nubFrom seen xs else x ∷ nubFrom (x ∷ seen) xs) → y ∈ x ∷ xs
    go true  m′          = there (nub-⊆ seen xs m′)
    go false (here e)    = here e
    go false (there m′)  = there (nub-⊆ (x ∷ seen) xs m′)

nub-fresh : ∀ seen xs {y} → y ∈ nubFrom seen xs → memberB y seen ≡ false
nub-fresh seen []       ()
nub-fresh seen (x ∷ xs) {y} m = go (memberB x seen) refl m
  where
    go : ∀ b → memberB x seen ≡ b → y ∈ (if b then nubFrom seen xs else x ∷ nubFrom (x ∷ seen) xs) → memberB y seen ≡ false
    go true  _ m′          = nub-fresh seen xs m′
    go false e (here refl) = e
    go false _ (there m′)  = member-false {y} {x} {seen} (nub-fresh (x ∷ seen) xs m′)

nub-unique : ∀ seen xs → Unique (nubFrom seen xs)
nub-unique seen []       = []
nub-unique seen (x ∷ xs) = go (memberB x seen)
  where
    fresh : All (x ≢_) (nubFrom (x ∷ seen) xs)
    fresh = All.tabulate (λ m e → member-ne (nub-fresh (x ∷ seen) xs m) (sym e))
    go : ∀ b → Unique (if b then nubFrom seen xs else x ∷ nubFrom (x ∷ seen) xs)
    go true  = nub-unique seen xs
    go false = fresh ∷ nub-unique (x ∷ seen) xs

-- In a list without repetition, an element's position is its index.
positionOf-lookup : ∀ (xs : List String) → Unique xs → ∀ i → positionOf (lookup xs i) xs ≡ just i
positionOf-lookup (x ∷ xs) u zero with x ≟ x
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
positionOf-lookup (x ∷ xs) (fx ∷ u) (suc i) with lookup xs i ≟ x
... | yes e = ⊥-elim (All.lookup fx (lookup-∈ xs i) (sym e))
... | no _  = cong (Maybe.map suc) (positionOf-lookup xs u i)

lookup-injective : ∀ (xs : List String) → Unique xs → Injective _≡_ _≡_ (lookup xs)
lookup-injective (x ∷ xs) u          {zero}  {zero}  _ = refl
lookup-injective (x ∷ xs) (fx ∷ u)   {zero}  {suc j} e = ⊥-elim (All.lookup fx (lookup-∈ xs j) e)
lookup-injective (x ∷ xs) (fx ∷ u)   {suc i} {zero}  e = ⊥-elim (All.lookup fx (lookup-∈ xs i) (sym e))
lookup-injective (x ∷ xs) (fx ∷ u)   {suc i} {suc j} e = cong suc (lookup-injective xs u e)

------------------------------------------------------------------------
-- A schema's parts
------------------------------------------------------------------------

module Parts (T : PolyType) where

  ps : List String
  ps = params T

  κ : ST.KCtx (arityOf T)
  κ = kindsOf T

  names : Fin (arityOf T) → String
  names = lookup ps

  ab : PolyType → ST.Ty (arityOf T)
  ab A = substPoly (rigidSubst T) A

  abF : PolyFunctor → ST.Fun (arityOf T)
  abF F = substPolyF (rigidSubst T) F

  private
    at : ∀ {x} → x ∈ ftv T → Σ[ j ∈ Fin (arityOf T) ] (positionOf x ps ≡ just j) × (lookup ps j ≡ x)
    at {x} m = positionOf-∈ x ps (∈-params T m)

  -- the variable of a parameter
  j : ∀ {x} → x ∈ ftv T → Fin (arityOf T)
  j m = proj₁ (at m)

  var-ab : ∀ {x} (m : x ∈ ftv T) → ptyS (rigidSubst T x) ≡ ST.var (j m)
  var-ab m = cong (maybe′ ST.var ST.Unit) (proj₁ (proj₂ (at m)))

  name-j : ∀ {x} (m : x ∈ ftv T) → names (j m) ≡ x
  name-j m = proj₂ (proj₂ (at m))

  in-ftv : ∀ i → names i ∈ ftv T
  in-ftv i = nub-⊆ [] (ftv T) (lookup-∈ ps i)

  j-names : ∀ i (m : names i ∈ ftv T) → j m ≡ i
  j-names i m = just-injective (trans (sym (proj₁ (proj₂ (at m)))) (positionOf-lookup ps (nub-unique [] (ftv T)) i))

  private
    occ-var : ∀ {a} {i k : Fin a} → Occurs i (ST.var k) → i ≡ k
    occ-var o-var = refl

    ˡ : ∀ {A B : List String} {x} → (∀ {y} → y ∈ A ++ B → y ∈ ftv T) → x ∈ A → x ∈ ftv T
    ˡ s m = s (∈-++⁺ˡ m)
    ʳ : ∀ (A : List String) {B : List String} {x} → (∀ {y} → y ∈ A ++ B → y ∈ ftv T) → x ∈ B → x ∈ ftv T
    ʳ A s m = s (∈-++⁺ʳ A m)

  -- The written part, read through the parameters' names.
  mutual
    reads : ∀ A → (∀ {x} → x ∈ ftv A → x ∈ ftv T) → TypeOf names (toPoly A) (ptyS (ab A))
    reads (PTVar x) s = subst (TypeOf names (SS.PTVar x)) (sym (var-ab (s (here refl)))) (to-var (j (s (here refl))) (name-j (s (here refl))))
    reads PUnit  _ = to-unit
    reads PVoid  _ = to-void
    reads PInt   _ = to-int
    reads PFloat _ = to-float
    reads (A P* B)      s = to-* (reads A (ˡ s)) (reads B (ʳ (ftv A) s))
    reads (A P+ B)      s = to-+ (reads A (ˡ s)) (reads B (ʳ (ftv A) s))
    reads (A P⇒[ q ] B) s = to-⇒ (reads A (ˡ s)) (reads B (ʳ (ftv A) s))
    reads (PEff A B)    s = to-eff (reads A (ˡ s)) (reads B (ʳ (ftv A) s))
    reads (PAct A B)    s = to-act (reads A (ˡ s)) (reads B (ʳ (ftv A) s))
    reads (Pμ-type F)   s = to-μ (readsF F s)
    reads (Pν-type F φ) s = to-ν (readsF F s)

    readsF : ∀ F → (∀ {x} → x ∈ ftvF F → x ∈ ftv T) → FunOf names (toPolyF F) (pfunS (abF F))
    readsF (PK A)   s = fo-K (reads A s)
    readsF PId      s = fo-Id
    readsF (F P⊕ G) s = fo-⊕ (readsF F (ˡ s)) (readsF G (ʳ (ftvF F) s))
    readsF (F P⊗ G) s = fo-⊗ (readsF F (ˡ s)) (readsF G (ʳ (ftvF F) s))

  -- A variable of the part occurs in it, at its parameter.
  mutual
    occ : ∀ A (s : ∀ {x} → x ∈ ftv A → x ∈ ftv T) {x} (m : x ∈ ftv A) → Occurs (j (s m)) (ptyS (ab A))
    occ (PTVar x) s (here refl) = subst (Occurs _) (sym (var-ab (s (here refl)))) o-var
    occ (A P* B)      s m = split A B s {λ k → Occurs k (ptyS (ab (A P* B)))} (λ m′ → o-*ˡ (occ A (ˡ s) m′)) (λ m′ → o-*ʳ (occ B (ʳ (ftv A) s) m′)) m
    occ (A P+ B)      s m = split A B s {λ k → Occurs k (ptyS (ab (A P+ B)))} (λ m′ → o-+ˡ (occ A (ˡ s) m′)) (λ m′ → o-+ʳ (occ B (ʳ (ftv A) s) m′)) m
    occ (A P⇒[ q ] B) s m = split A B s {λ k → Occurs k (ptyS (ab (A P⇒[ q ] B)))} (λ m′ → o-⇒ˡ (occ A (ˡ s) m′)) (λ m′ → o-⇒ʳ (occ B (ʳ (ftv A) s) m′)) m
    occ (PEff A B)    s m = split A B s {λ k → Occurs k (ptyS (ab (PEff A B)))} (λ m′ → o-⇒ˡ (occ A (ˡ s) m′)) (λ m′ → o-⇒ʳ (occ B (ʳ (ftv A) s) m′)) m
    occ (PAct A B)    s m = split A B s {λ k → Occurs k (ptyS (ab (PAct A B)))} (λ m′ → o-⇒ˡ (occ A (ˡ s) m′)) (λ m′ → o-⇒ʳ (occ B (ʳ (ftv A) s) m′)) m
    occ (Pμ-type F)   s m = o-μ (occF F s m)
    occ (Pν-type F φ) s m = o-ν (occF F s m)

    occF : ∀ F (s : ∀ {x} → x ∈ ftvF F → x ∈ ftv T) {x} (m : x ∈ ftvF F) → OccursF (j (s m)) (pfunS (abF F))
    occF (PK A)   s m = o-K (occ A s m)
    occF (F P⊕ G) s m = splitF F G s {λ k → OccursF k (pfunS (abF (F P⊕ G)))} (λ m′ → o-⊕ˡ (occF F (ˡ s) m′)) (λ m′ → o-⊕ʳ (occF G (ʳ (ftvF F) s) m′)) m
    occF (F P⊗ G) s m = splitF F G s {λ k → OccursF k (pfunS (abF (F P⊗ G)))} (λ m′ → o-⊗ˡ (occF F (ˡ s) m′)) (λ m′ → o-⊗ʳ (occF G (ʳ (ftvF F) s) m′)) m

    -- a variable of `A ++ B`: of one side (the parameter is the same)
    split : ∀ A B (s : ∀ {x} → x ∈ ftv A ++ ftv B → x ∈ ftv T) {P : Fin (arityOf T) → Set}
          → (∀ {x} (m : x ∈ ftv A) → P (j (ˡ s m))) → (∀ {x} (m : x ∈ ftv B) → P (j (ʳ (ftv A) s m)))
          → ∀ {x} (m : x ∈ ftv A ++ ftv B) → P (j (s m))
    split A B s {P} l r m = side (∈-++⁻ (ftv A) m) m
      where
        side : ∀ {x} → (x ∈ ftv A) Data.Sum.⊎ (x ∈ ftv B) → (m′ : x ∈ ftv A ++ ftv B) → P (j (s m′))
        side (inj₁ ma) m′ = subst P (j-irr (ˡ s ma) (s m′)) (l ma)
        side (inj₂ mb) m′ = subst P (j-irr (ʳ (ftv A) s mb) (s m′)) (r mb)

    splitF : ∀ F G (s : ∀ {x} → x ∈ ftvF F ++ ftvF G → x ∈ ftv T) {P : Fin (arityOf T) → Set}
           → (∀ {x} (m : x ∈ ftvF F) → P (j (ˡ s m))) → (∀ {x} (m : x ∈ ftvF G) → P (j (ʳ (ftvF F) s m)))
           → ∀ {x} (m : x ∈ ftvF F ++ ftvF G) → P (j (s m))
    splitF F G s {P} l r m = side (∈-++⁻ (ftvF F) m) m
      where
        side : ∀ {x} → (x ∈ ftvF F) Data.Sum.⊎ (x ∈ ftvF G) → (m′ : x ∈ ftvF F ++ ftvF G) → P (j (s m′))
        side (inj₁ ma) m′ = subst P (j-irr (ˡ s ma) (s m′)) (l ma)
        side (inj₂ mb) m′ = subst P (j-irr (ʳ (ftvF F) s mb) (s m′)) (r mb)

    -- a parameter's variable does not depend on the membership proof
    j-irr : ∀ {x} (m m′ : x ∈ ftv T) → j m ≡ j m′
    j-irr m m′ = just-injective (trans (sym (proj₁ (proj₂ (at m)))) (proj₁ (proj₂ (at m′))))

  -- A variable occurring in the part is one of the part's.
  mutual
    occ⁻ : ∀ A (s : ∀ {x} → x ∈ ftv A → x ∈ ftv T) {i} → Occurs i (ptyS (ab A)) → names i ∈ ftv A
    occ⁻ (PTVar x) s {i} o =
      subst (_∈ (x ∷ [])) (sym (trans (cong names (occ-var (subst (Occurs i) (var-ab (s (here refl))) o))) (name-j (s (here refl))))) (here refl)
    occ⁻ (A P* B) s (o-*ˡ o)      = ∈-++⁺ˡ (occ⁻ A (ˡ s) o)
    occ⁻ (A P* B) s (o-*ʳ o)      = ∈-++⁺ʳ (ftv A) (occ⁻ B (ʳ (ftv A) s) o)
    occ⁻ (A P+ B) s (o-+ˡ o)      = ∈-++⁺ˡ (occ⁻ A (ˡ s) o)
    occ⁻ (A P+ B) s (o-+ʳ o)      = ∈-++⁺ʳ (ftv A) (occ⁻ B (ʳ (ftv A) s) o)
    occ⁻ (A P⇒[ q ] B) s (o-⇒ˡ o) = ∈-++⁺ˡ (occ⁻ A (ˡ s) o)
    occ⁻ (A P⇒[ q ] B) s (o-⇒ʳ o) = ∈-++⁺ʳ (ftv A) (occ⁻ B (ʳ (ftv A) s) o)
    occ⁻ (PEff A B) s (o-⇒ˡ o)    = ∈-++⁺ˡ (occ⁻ A (ˡ s) o)
    occ⁻ (PEff A B) s (o-⇒ʳ o)    = ∈-++⁺ʳ (ftv A) (occ⁻ B (ʳ (ftv A) s) o)
    occ⁻ (PAct A B) s (o-⇒ˡ o)    = ∈-++⁺ˡ (occ⁻ A (ˡ s) o)
    occ⁻ (PAct A B) s (o-⇒ʳ o)    = ∈-++⁺ʳ (ftv A) (occ⁻ B (ʳ (ftv A) s) o)
    occ⁻ (Pμ-type F) s (o-μ o)    = occF⁻ F s o
    occ⁻ (Pν-type F φ) s (o-ν o)  = occF⁻ F s o

    occF⁻ : ∀ F (s : ∀ {x} → x ∈ ftvF F → x ∈ ftv T) {i} → OccursF i (pfunS (abF F)) → names i ∈ ftvF F
    occF⁻ (PK A) s (o-K o)      = occ⁻ A s o
    occF⁻ (F P⊕ G) s (o-⊕ˡ o)   = ∈-++⁺ˡ (occF⁻ F (ˡ s) o)
    occF⁻ (F P⊕ G) s (o-⊕ʳ o)   = ∈-++⁺ʳ (ftvF F) (occF⁻ G (ʳ (ftvF F) s) o)
    occF⁻ (F P⊗ G) s (o-⊗ˡ o)   = ∈-++⁺ˡ (occF⁻ F (ˡ s) o)
    occF⁻ (F P⊗ G) s (o-⊗ʳ o)   = ∈-++⁺ʳ (ftvF F) (occF⁻ G (ʳ (ftvF F) s) o)

  -- …at any of its parameters' indices.
  occ-at : ∀ A (s : ∀ {x} → x ∈ ftv A → x ∈ ftv T) i → names i ∈ ftv A → Occurs i (ptyS (ab A))
  occ-at A s i m = subst (λ k → Occurs k (ptyS (ab A))) (trans (j-irr (s m) (in-ftv i)) (j-names i (in-ftv i))) (occ A s m)

  -- Under a functor constant: exactly the variables `ftvK` lists.
  mutual
    underK⁻ : ∀ A (s : ∀ {x} → x ∈ ftv A → x ∈ ftv T) {i} → UnderK i (ptyS (ab A)) → names i ∈ ftvK A
    underK⁻ (A P* B) s (uk-*ˡ u)      = ∈-++⁺ˡ (underK⁻ A (ˡ s) u)
    underK⁻ (A P* B) s (uk-*ʳ u)      = ∈-++⁺ʳ (ftvK A) (underK⁻ B (ʳ (ftv A) s) u)
    underK⁻ (A P+ B) s (uk-+ˡ u)      = ∈-++⁺ˡ (underK⁻ A (ˡ s) u)
    underK⁻ (A P+ B) s (uk-+ʳ u)      = ∈-++⁺ʳ (ftvK A) (underK⁻ B (ʳ (ftv A) s) u)
    underK⁻ (A P⇒[ q ] B) s (uk-⇒ˡ u) = ∈-++⁺ˡ (underK⁻ A (ˡ s) u)
    underK⁻ (A P⇒[ q ] B) s (uk-⇒ʳ u) = ∈-++⁺ʳ (ftvK A) (underK⁻ B (ʳ (ftv A) s) u)
    underK⁻ (PEff A B) s (uk-⇒ˡ u)    = ∈-++⁺ˡ (underK⁻ A (ˡ s) u)
    underK⁻ (PEff A B) s (uk-⇒ʳ u)    = ∈-++⁺ʳ (ftvK A) (underK⁻ B (ʳ (ftv A) s) u)
    underK⁻ (PAct A B) s (uk-⇒ˡ u)    = ∈-++⁺ˡ (underK⁻ A (ˡ s) u)
    underK⁻ (PAct A B) s (uk-⇒ʳ u)    = ∈-++⁺ʳ (ftvK A) (underK⁻ B (ʳ (ftv A) s) u)
    underK⁻ (Pμ-type F) s (uk-μ u)    = underKF⁻ F s u
    underK⁻ (Pν-type F φ) s (uk-ν u)  = underKF⁻ F s u
    underK⁻ (PTVar x) s {i} u = ⊥-elim (no-var (subst (UnderK i) (var-ab (s (here refl))) u))
      where
        no-var : ∀ {k} → UnderK i (ST.var k) → ⊥
        no-var ()

    underKF⁻ : ∀ F (s : ∀ {x} → x ∈ ftvF F → x ∈ ftv T) {i} → UnderKF i (pfunS (abF F)) → names i ∈ ftvKF F
    underKF⁻ (PK A) s (uk-K o)     = occ⁻ A s o
    underKF⁻ (F P⊕ G) s (uk-⊕ˡ u)  = ∈-++⁺ˡ (underKF⁻ F (ˡ s) u)
    underKF⁻ (F P⊕ G) s (uk-⊕ʳ u)  = ∈-++⁺ʳ (ftvKF F) (underKF⁻ G (ʳ (ftvF F) s) u)
    underKF⁻ (F P⊗ G) s (uk-⊗ˡ u)  = ∈-++⁺ˡ (underKF⁻ F (ˡ s) u)
    underKF⁻ (F P⊗ G) s (uk-⊗ʳ u)  = ∈-++⁺ʳ (ftvKF F) (underKF⁻ G (ʳ (ftvF F) s) u)

  mutual
    underK : ∀ A (s : ∀ {x} → x ∈ ftv A → x ∈ ftv T) i → names i ∈ ftvK A → UnderK i (ptyS (ab A))
    underK (A P* B) s i m = sideK (∈-++⁻ (ftvK A) m) (λ m′ → uk-*ˡ (underK A (ˡ s) i m′)) (λ m′ → uk-*ʳ (underK B (ʳ (ftv A) s) i m′))
    underK (A P+ B) s i m = sideK (∈-++⁻ (ftvK A) m) (λ m′ → uk-+ˡ (underK A (ˡ s) i m′)) (λ m′ → uk-+ʳ (underK B (ʳ (ftv A) s) i m′))
    underK (A P⇒[ q ] B) s i m = sideK (∈-++⁻ (ftvK A) m) (λ m′ → uk-⇒ˡ (underK A (ˡ s) i m′)) (λ m′ → uk-⇒ʳ (underK B (ʳ (ftv A) s) i m′))
    underK (PEff A B) s i m = sideK (∈-++⁻ (ftvK A) m) (λ m′ → uk-⇒ˡ (underK A (ˡ s) i m′)) (λ m′ → uk-⇒ʳ (underK B (ʳ (ftv A) s) i m′))
    underK (PAct A B) s i m = sideK (∈-++⁻ (ftvK A) m) (λ m′ → uk-⇒ˡ (underK A (ˡ s) i m′)) (λ m′ → uk-⇒ʳ (underK B (ʳ (ftv A) s) i m′))
    underK (Pμ-type F) s i m = uk-μ (underKF F s i m)
    underK (Pν-type F φ) s i m = uk-ν (underKF F s i m)

    underKF : ∀ F (s : ∀ {x} → x ∈ ftvF F → x ∈ ftv T) i → names i ∈ ftvKF F → UnderKF i (pfunS (abF F))
    underKF (PK A) s i m = uk-K (occ-at A s i m)
    underKF (F P⊕ G) s i m = sideK (∈-++⁻ (ftvKF F) m) (λ m′ → uk-⊕ˡ (underKF F (ˡ s) i m′)) (λ m′ → uk-⊕ʳ (underKF G (ʳ (ftvF F) s) i m′))
    underKF (F P⊗ G) s i m = sideK (∈-++⁻ (ftvKF F) m) (λ m′ → uk-⊗ˡ (underKF F (ˡ s) i m′)) (λ m′ → uk-⊗ʳ (underKF G (ʳ (ftvF F) s) i m′))

    sideK : ∀ {a b : Set} {P : Set} → a Data.Sum.⊎ b → (a → P) → (b → P) → P
    sideK (inj₁ x) f g = f x
    sideK (inj₂ y) f g = g y

------------------------------------------------------------------------
-- The schema
------------------------------------------------------------------------

schemaOf-S : ∀ T → SchemaOf (toPoly T) (schS (schemaOf T))
schemaOf-S T = record
  { names    = names
  ; distinct = lookup-injective ps (nub-unique [] (ftv T))
  ; reads    = reads T (λ m → m)
  ; used     = λ i → occ-at T (λ m → m) i (in-ftv i)
  ; kinded   = λ i → (λ u → to-base i (memberB-complete _ (ftvK T) (underK⁻ T (λ m → m) u)))
                   , (λ e → underK T (λ m → m) i (from-base i (memberB _ (ftvK T)) refl e))
  }
  where
    open Parts T
    to-base : ∀ i → memberB (names i) (ftvK T) ≡ true → kindsS κ i ≡ ST.base
    to-base i e = cong (λ b → if b then LT.k-base else LT.k-any) e
    from-base : ∀ i b → memberB (names i) (ftvK T) ≡ b → (if b then LT.k-base else LT.k-any) ≡ ST.base
              → names i ∈ ftvK T
    from-base i true  e _  = memberB-sound _ (ftvK T) e
    from-base i false _ ()

------------------------------------------------------------------------
-- What the front-end bridge asks of a telescope entry
------------------------------------------------------------------------

ftv-empty : ∀ {xs : List String} → (∀ {x} → x ∈ xs → ⊥) → xs ≡ []
ftv-empty {[]}     _ = refl
ftv-empty {x ∷ xs} n = ⊥-elim (n (here refl))

mutual
  empty-ground : ∀ A → ftv A ≡ [] → Ground A
  empty-ground PUnit  _ = tt
  empty-ground PVoid  _ = tt
  empty-ground PInt   _ = tt
  empty-ground PFloat _ = tt
  empty-ground (PTVar x) ()
  empty-ground (A P* B)      e = empty-ground A (++-conicalˡ (ftv A) (ftv B) e) , empty-ground B (++-conicalʳ (ftv A) (ftv B) e)
  empty-ground (A P+ B)      e = empty-ground A (++-conicalˡ (ftv A) (ftv B) e) , empty-ground B (++-conicalʳ (ftv A) (ftv B) e)
  empty-ground (A P⇒[ q ] B) e = empty-ground A (++-conicalˡ (ftv A) (ftv B) e) , empty-ground B (++-conicalʳ (ftv A) (ftv B) e)
  empty-ground (PEff A B)    e = empty-ground A (++-conicalˡ (ftv A) (ftv B) e) , empty-ground B (++-conicalʳ (ftv A) (ftv B) e)
  empty-ground (PAct A B)    e = empty-ground A (++-conicalˡ (ftv A) (ftv B) e) , empty-ground B (++-conicalʳ (ftv A) (ftv B) e)
  empty-ground (Pμ-type F)   e = empty-groundF F e
  empty-ground (Pν-type F φ) e = empty-groundF F e

  empty-groundF : ∀ F → ftvF F ≡ [] → GroundF F
  empty-groundF (PK A)   e = empty-ground A e
  empty-groundF PId      _ = tt
  empty-groundF (F P⊕ G) e = empty-groundF F (++-conicalˡ (ftvF F) (ftvF G) e) , empty-groundF G (++-conicalʳ (ftvF F) (ftvF G) e)
  empty-groundF (F P⊗ G) e = empty-groundF F (++-conicalˡ (ftvF F) (ftvF G) e) , empty-groundF G (++-conicalʳ (ftvF F) (ftvF G) e)

ground-arity : ∀ sc → Ground sc → arityOf sc ≡ 0
ground-arity sc g = cong (λ l → length (nubFrom [] l)) (ftv-empty (ftv-ground sc g))

open-arity : ∀ sc → ¬ Ground sc → 0 < arityOf sc
open-arity sc ng = go (ftv sc) refl
  where
    go : ∀ l → ftv sc ≡ l → 0 < arityOf sc
    go []      e = ⊥-elim (ng (empty-ground sc e))
    go (x ∷ l) e = subst (λ l′ → 0 < length (nubFrom [] l′)) (sym e) (s≤s z≤n)

-- Every parameter occurs in the schema's type.
schema-occ : ∀ sc i → Occurs i (ptyS (SC.Schema.type (schemaOf sc)))
schema-occ sc = SchemaOf.used (schemaOf-S sc)

private
  -- (the arrow's two halves are the schema's parts)
  incl′ : ∀ sc sd sco → (∀ {x} → x ∈ ftv sd ++ ftv sco → x ∈ ftv sc) → CodVarsInDom sd sco
        → ∀ i → Occurs i (ptyS (Parts.ab sc sco)) → Occurs i (ptyS (Parts.ab sc sd))
  incl′ sc sd sco s cv i o =
    Parts.occ-at sc sd (λ m → s (∈-++⁺ˡ m)) i (cv (Parts.occ⁻ sc sco (λ m → s (∈-++⁺ʳ (ftv sd) m)) o))

-- An arrow schema is an arrow; its codomain's variables occur in its domain.
schema-arrow : ∀ sc {sd sco π′} → ArrowSchema sc sd sco π′ → CodVarsInDom sd sco
             → Σ[ X ∈ ST.Ty (arityOf sc) ] Σ[ Y ∈ ST.Ty (arityOf sc) ]
                 (SC.Schema.type (schemaOf sc) ≡ X ST.⇒[ mk-kind Many π′ ] Y)
                 × (∀ i → Occurs i (ptyS Y) → Occurs i (ptyS X))
schema-arrow (sd P⇒[ Many ] sco) as-pure cv = Parts.ab (sd P⇒[ Many ] sco) sd , Parts.ab (sd P⇒[ Many ] sco) sco , refl , incl′ (sd P⇒[ Many ] sco) sd sco (λ m → m) cv
schema-arrow (PEff sd sco) as-eff cv = Parts.ab (PEff sd sco) sd , Parts.ab (PEff sd sco) sco , refl , incl′ (PEff sd sco) sd sco (λ m → m) cv
schema-arrow (PAct sd sco) as-act cv = Parts.ab (PAct sd sco) sd , Parts.ab (PAct sd sco) sco , refl , incl′ (PAct sd sco) sd sco (λ m → m) cv
