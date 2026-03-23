------------------------------------------------------------------------
-- CataFree: Predicate for Terms Without Cata
--
-- This module defines the CataFree predicate, which holds for terms
-- that contain no cata constructor. This is crucial for our restricted
-- confluence proof:
--
--   1. encode t produces terms that are cata-free
--   2. CCC reduction preserves cata-free property
--   3. The only cata in (normalize ∘ encode t) comes from normalize itself
--
-- This allows us to factor reductions and apply different confluence
-- proofs to the cata and CCC parts separately.
------------------------------------------------------------------------

module normalizer.Theory.StandardCCCExtension.CataFree where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata; fmap;
         _⟶_; _⟶*_; done; step)
open import normalizer.Encoding.Encoding
  using (encode; ⌜_⌝Ty; ⌜_⌝Func; TyFuncCode; TermCode')
open import normalizer.Axioms.StandardCCC
  using (_⟶ccc_; _⟶*ccc_; done-ccc; step-ccc)

------------------------------------------------------------------------
-- CataFree Predicate
--
-- A term is cata-free if it contains no cata subterms.
-- Defined inductively: all constructors except cata are included.
------------------------------------------------------------------------

data CataFree : ∀ {A B} → Term A B → Set where
  cf-id       : ∀ {A} → CataFree (id {A})
  cf-comp     : ∀ {A B C} {f : Term B C} {g : Term A B} →
                CataFree f → CataFree g → CataFree (f ∘ g)
  cf-fst      : ∀ {A B} → CataFree (fst {A} {B})
  cf-snd      : ∀ {A B} → CataFree (snd {A} {B})
  cf-pair     : ∀ {A B C} {f : Term C A} {g : Term C B} →
                CataFree f → CataFree g → CataFree ⟨ f , g ⟩
  cf-inl      : ∀ {A B} → CataFree (inl {A} {B})
  cf-inr      : ∀ {A B} → CataFree (inr {A} {B})
  cf-case     : ∀ {A B C} {f : Term A C} {g : Term B C} →
                CataFree f → CataFree g → CataFree [ f , g ]
  cf-terminal : ∀ {A} → CataFree (terminal {A})
  cf-initial  : ∀ {A} → CataFree (initial {A})
  cf-In       : ∀ {F} → CataFree (In {F})
  cf-Out      : ∀ {F} → CataFree (Out {F})
  cf-curry    : ∀ {A B C} {f : Term (A * B) C} →
                CataFree f → CataFree (curry f)
  cf-apply    : ∀ {A B} → CataFree (apply {A} {B})
  -- NOTE: No cf-cata constructor! That's the key property.

------------------------------------------------------------------------
-- Type/Functor Encodings are CataFree
--
-- The encoding of types and functors uses In, inl, inr, terminal, ⟨_,_⟩
-- - all of which are cata-free.
------------------------------------------------------------------------

⌜⌝Ty-catafree : ∀ (A : Ty) → CataFree (⌜ A ⌝Ty)
⌜⌝Func-catafree : ∀ (F : Func) → CataFree (⌜ F ⌝Func)

-- Void: In ∘ inl ∘ terminal
⌜⌝Ty-catafree Void = cf-comp cf-In (cf-comp cf-inl cf-terminal)

-- Unit: In ∘ inr ∘ inl ∘ terminal
⌜⌝Ty-catafree Unit = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inl cf-terminal))

-- Product: In ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩
⌜⌝Ty-catafree (A * B) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B)))))

-- Sum: In ∘ inr ∘ inr ∘ inr ∘ inl ∘ ⟨...⟩
⌜⌝Ty-catafree (A + B) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B))))))

-- Exponential: In ∘ inr^4 ∘ inl ∘ ⟨...⟩
⌜⌝Ty-catafree (A ⇒ B) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B)))))))

-- Mu: In ∘ inr^5 ∘ inl ∘ ⌜F⌝
⌜⌝Ty-catafree (μ F) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (⌜⌝Func-catafree F)))))))

-- Id functor: In ∘ inr^6 ∘ inl ∘ terminal
⌜⌝Func-catafree Id = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  cf-terminal)))))))

-- K functor: In ∘ inr^7 ∘ inl ∘ ⌜A⌝
⌜⌝Func-catafree (K A) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (⌜⌝Ty-catafree A)))))))))

-- ⊕ functor: In ∘ inr^8 ∘ inl ∘ ⟨...⟩
⌜⌝Func-catafree (F ⊕ G) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Func-catafree F) (⌜⌝Func-catafree G)))))))))))

-- ⊗ functor: In ∘ inr^9 ∘ ⟨...⟩
⌜⌝Func-catafree (F ⊗ G) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr
  (cf-pair (⌜⌝Func-catafree F) (⌜⌝Func-catafree G)))))))))))

------------------------------------------------------------------------
-- KEY LEMMA: Encoded Terms are CataFree
--
-- The encode function never produces cata - it uses only In, inl, inr,
-- ⟨_,_⟩, terminal, and ∘ to represent terms as data.
------------------------------------------------------------------------

encode-is-catafree : ∀ {A B} (t : Term A B) → CataFree (encode t)

-- 0: id - In ∘ inl ∘ ⌜A⌝
encode-is-catafree (id {A}) = cf-comp cf-In (cf-comp cf-inl (⌜⌝Ty-catafree A))

-- 1: compose - In ∘ inr ∘ inl ∘ ⟨encode f, encode g⟩
encode-is-catafree (f ∘ g) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (encode-is-catafree f) (encode-is-catafree g))))

-- 2: fst - In ∘ inr^2 ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
encode-is-catafree (fst {A} {B}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B)))))

-- 3: snd - In ∘ inr^3 ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
encode-is-catafree (snd {A} {B}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B))))))

-- 4: pair - In ∘ inr^4 ∘ inl ∘ ⟨encode f, encode g⟩
encode-is-catafree ⟨ f , g ⟩ = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (encode-is-catafree f) (encode-is-catafree g)))))))

-- 5: inl - In ∘ inr^5 ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
encode-is-catafree (inl {A} {B}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B))))))))

-- 6: inr - In ∘ inr^6 ∘ inl ∘ ⟨⌜A⌝, ⌜B⌝⟩
encode-is-catafree (inr {A} {B}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B)))))))))

-- 7: case - In ∘ inr^7 ∘ inl ∘ ⟨encode f, encode g⟩
encode-is-catafree [ f , g ] = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (encode-is-catafree f) (encode-is-catafree g))))))))))

-- 8: terminal - In ∘ inr^8 ∘ inl ∘ ⌜A⌝
encode-is-catafree (terminal {A}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (⌜⌝Ty-catafree A))))))))))

-- 9: initial - In ∘ inr^9 ∘ inl ∘ ⌜A⌝
encode-is-catafree (initial {A}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (⌜⌝Ty-catafree A)))))))))))

-- 10: In - In ∘ inr^10 ∘ inl ∘ ⌜F⌝
encode-is-catafree (In {F}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (⌜⌝Func-catafree F))))))))))))

-- 11: Out - In ∘ inr^11 ∘ inl ∘ ⌜F⌝
encode-is-catafree (Out {F}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (⌜⌝Func-catafree F)))))))))))))

-- 12: cata - In ∘ inr^12 ∘ inl ∘ ⟨⌜F⌝, encode alg⟩
encode-is-catafree (cata F alg) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair (⌜⌝Func-catafree F) (encode-is-catafree alg)))))))))))))))

-- 13: curry - In ∘ inr^13 ∘ inl ∘ ⟨⟨⌜A⌝, ⌜B⌝⟩, ⟨⌜C⌝, encode f⟩⟩
encode-is-catafree (curry {A} {B} {C} f) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inl
  (cf-pair
    (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B))
    (cf-pair (⌜⌝Ty-catafree C) (encode-is-catafree f)))))))))))))))))

-- 14: apply - In ∘ inr^14 ∘ ⟨⌜A⌝, ⌜B⌝⟩
encode-is-catafree (apply {A} {B}) = cf-comp cf-In (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr (cf-comp cf-inr
  (cf-pair (⌜⌝Ty-catafree A) (⌜⌝Ty-catafree B))))))))))))))))

------------------------------------------------------------------------
-- CCC Reduction Preserves CataFree
--
-- Since CCC reduction doesn't introduce cata (no cata rules in CCC
-- reduction), reducing a cata-free term yields a cata-free term.
------------------------------------------------------------------------

ccc-preserves-catafree : ∀ {A B} {t u : Term A B} →
                         CataFree t → t ⟶ccc u → CataFree u
-- Identity laws
ccc-preserves-catafree (cf-comp _ cff) _⟶ccc_.ccc-id-left = cff
ccc-preserves-catafree (cf-comp cff _) _⟶ccc_.ccc-id-right = cff

-- Product laws
ccc-preserves-catafree (cf-comp _ (cf-pair cff _)) _⟶ccc_.ccc-fst-pair = cff
ccc-preserves-catafree (cf-comp _ (cf-pair _ cfg)) _⟶ccc_.ccc-snd-pair = cfg
ccc-preserves-catafree (cf-pair _ _) _⟶ccc_.ccc-eta-pair = cf-id

-- Coproduct laws
ccc-preserves-catafree (cf-comp (cf-case cff _) _) _⟶ccc_.ccc-case-inl = cff
ccc-preserves-catafree (cf-comp (cf-case _ cfg) _) _⟶ccc_.ccc-case-inr = cfg
ccc-preserves-catafree (cf-case _ _) _⟶ccc_.ccc-eta-case = cf-id

-- Pair distribution
ccc-preserves-catafree (cf-comp (cf-pair cff cfg) cfh) _⟶ccc_.ccc-pair-comp =
  cf-pair (cf-comp cff cfh) (cf-comp cfg cfh)

-- Exponential laws
ccc-preserves-catafree (cf-comp _ (cf-pair (cf-curry cff) cfg)) _⟶ccc_.ccc-curry-β =
  cf-comp cff (cf-pair cf-id cfg)
ccc-preserves-catafree (cf-comp _ (cf-pair (cf-comp (cf-curry cff) cfh) cfg)) _⟶ccc_.ccc-curry-β-ext =
  cf-comp cff (cf-pair cfh cfg)
ccc-preserves-catafree (cf-curry (cf-comp _ (cf-pair (cf-comp cff _) _))) _⟶ccc_.ccc-curry-η = cff

-- Associativity
ccc-preserves-catafree (cf-comp cff (cf-comp cfg cfh)) _⟶ccc_.ccc-assoc-l =
  cf-comp (cf-comp cff cfg) cfh
ccc-preserves-catafree (cf-comp (cf-comp cff cfg) cfh) _⟶ccc_.ccc-assoc-r =
  cf-comp cff (cf-comp cfg cfh)

-- Congruence rules
ccc-preserves-catafree (cf-comp cff cfg) (_⟶ccc_.ccc-∘-l r) =
  cf-comp (ccc-preserves-catafree cff r) cfg
ccc-preserves-catafree (cf-comp cff cfg) (_⟶ccc_.ccc-∘-r r) =
  cf-comp cff (ccc-preserves-catafree cfg r)
ccc-preserves-catafree (cf-pair cff cfg) (_⟶ccc_.ccc-pair-l r) =
  cf-pair (ccc-preserves-catafree cff r) cfg
ccc-preserves-catafree (cf-pair cff cfg) (_⟶ccc_.ccc-pair-r r) =
  cf-pair cff (ccc-preserves-catafree cfg r)
ccc-preserves-catafree (cf-case cff cfg) (_⟶ccc_.ccc-case-l r) =
  cf-case (ccc-preserves-catafree cff r) cfg
ccc-preserves-catafree (cf-case cff cfg) (_⟶ccc_.ccc-case-r r) =
  cf-case cff (ccc-preserves-catafree cfg r)
ccc-preserves-catafree (cf-curry cff) (_⟶ccc_.ccc-curry r) =
  cf-curry (ccc-preserves-catafree cff r)

-- Multi-step preservation
ccc*-preserves-catafree : ∀ {A B} {t u : Term A B} →
                          CataFree t → t ⟶*ccc u → CataFree u
ccc*-preserves-catafree cft done-ccc = cft
ccc*-preserves-catafree cft (step-ccc r rs) =
  ccc*-preserves-catafree (ccc-preserves-catafree cft r) rs

------------------------------------------------------------------------
-- Summary
--
-- Key results:
--   encode-is-catafree    : ∀ t → CataFree (encode t)
--   ccc-preserves-catafree  : CataFree t → t ⟶ccc u → CataFree u
--   ccc*-preserves-catafree : CataFree t → t ⟶*ccc u → CataFree u
--
-- These establish that:
--   1. Encoded terms have no cata
--   2. CCC reduction never introduces cata
--   3. Therefore the cata in (cata F alg ∘ encode t) remains isolated
------------------------------------------------------------------------
