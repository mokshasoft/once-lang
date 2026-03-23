------------------------------------------------------------------------
-- TermFunctor: TermF-specific but reusable infrastructure
--
-- This module defines the TermF functor decomposition for navigating
-- through the 15-position encoding of CCC terms. While specific to
-- the Term encoding, these definitions are reusable for any CCC
-- tool that uses this encoding (normalizers, compilers, optimizers).
--
-- Position mapping:
--   0: id       (K TyFuncCode)
--   1: comp     (Id ⊗ Id)
--   2: fst      (K TyFuncCode ⊗ K TyFuncCode)
--   3: snd      (K TyFuncCode ⊗ K TyFuncCode)
--   4: pair     (Id ⊗ Id)
--   5: inl      (K TyFuncCode ⊗ K TyFuncCode)
--   6: inr      (K TyFuncCode ⊗ K TyFuncCode)
--   7: case     (Id ⊗ Id)
--   8: terminal (K TyFuncCode)
--   9: initial  (K TyFuncCode)
--  10: In       (K TyFuncCode)
--  11: Out      (K TyFuncCode)
--  12: cata     (K TyFuncCode ⊗ Id)
--  13: curry    ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))
--  14: apply    (K TyFuncCode ⊗ K TyFuncCode)
------------------------------------------------------------------------

module normalizer.Encoding.TermFunctor where

open import normalizer.Combinators.OutIn public
open import normalizer.Encoding.Encoding
  using (TyFuncCode; TermCode'; TermF) public

------------------------------------------------------------------------
-- Progressive TermF decomposition
--
-- TermF-N represents the functor for positions N and beyond.
-- This decomposition allows efficient navigation through the
-- injection chain during proofs.
------------------------------------------------------------------------

-- The rest of TermF after K TyFuncCode (positions 1-14)
TermF-rest : Func
TermF-rest = (Id ⊗ Id)                                   -- 1: f ∘ g
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst A B
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd A B
           ⊕ (Id ⊗ Id)                                   -- 4: ⟨f, g⟩
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl A B
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr A B
           ⊕ (Id ⊗ Id)                                   -- 7: [f, g]
           ⊕ (K TyFuncCode)                              -- 8: terminal A
           ⊕ (K TyFuncCode)                              -- 9: initial A
           ⊕ (K TyFuncCode)                              -- 10: In F
           ⊕ (K TyFuncCode)                              -- 11: Out F
           ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata F alg
           ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
           ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

-- TermF = K TyFuncCode ⊕ TermF-rest
TermF-decomp : TermF ≡ (K TyFuncCode ⊕ TermF-rest)
TermF-decomp = refl

-- Nested functors for each depth level
TermF-1 : Func  -- After 1 inr (positions 1-14)
TermF-1 = (Id ⊗ Id)                                   -- 1: comp
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd
        ⊕ (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-2 : Func  -- After 2 inrs (positions 2-14)
TermF-2 = (K TyFuncCode ⊗ K TyFuncCode)              -- 2: fst
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd
        ⊕ (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-3 : Func  -- After 3 inrs (positions 3-14)
TermF-3 = (K TyFuncCode ⊗ K TyFuncCode)              -- 3: snd
        ⊕ (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-4 : Func  -- After 4 inrs (positions 4-14)
TermF-4 = (Id ⊗ Id)                                   -- 4: pair
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-5 : Func  -- After 5 inrs (positions 5-14)
TermF-5 = (K TyFuncCode ⊗ K TyFuncCode)              -- 5: inl
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-6 : Func  -- After 6 inrs (positions 6-14)
TermF-6 = (K TyFuncCode ⊗ K TyFuncCode)              -- 6: inr
        ⊕ (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-7 : Func  -- After 7 inrs (positions 7-14)
TermF-7 = (Id ⊗ Id)                                   -- 7: case
        ⊕ (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-8 : Func  -- After 8 inrs (positions 8-14)
TermF-8 = (K TyFuncCode)                              -- 8: terminal
        ⊕ (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-9 : Func  -- After 9 inrs (positions 9-14)
TermF-9 = (K TyFuncCode)                              -- 9: initial
        ⊕ (K TyFuncCode)                              -- 10: In
        ⊕ (K TyFuncCode)                              -- 11: Out
        ⊕ (K TyFuncCode ⊗ Id)                        -- 12: cata
        ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
        ⊕ (K TyFuncCode ⊗ K TyFuncCode)              -- 14: apply

TermF-10 : Func  -- After 10 inrs (positions 10-14)
TermF-10 = (K TyFuncCode)                             -- 10: In
         ⊕ (K TyFuncCode)                             -- 11: Out
         ⊕ (K TyFuncCode ⊗ Id)                       -- 12: cata
         ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-11 : Func  -- After 11 inrs (positions 11-14)
TermF-11 = (K TyFuncCode)                             -- 11: Out
         ⊕ (K TyFuncCode ⊗ Id)                       -- 12: cata
         ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-12 : Func  -- After 12 inrs (positions 12-14)
TermF-12 = (K TyFuncCode ⊗ Id)                       -- 12: cata
         ⊕ ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-13 : Func  -- After 13 inrs (positions 13-14)
TermF-13 = ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id))  -- 13: curry
         ⊕ (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

TermF-14 : Func  -- After 14 inrs (position 14 only)
TermF-14 = (K TyFuncCode ⊗ K TyFuncCode)             -- 14: apply

------------------------------------------------------------------------
-- fmap distribution through inr chains
--
-- For each level, fmap F f ∘ inr ⟶* inr ∘ fmap G f
------------------------------------------------------------------------

fmap-TermF-inl : ∀ {A B} (f : Term A B) →
                 (fmap TermF f ∘ inl) ⟶* inl
fmap-TermF-inl f =
  -- fmap TermF f = fmap (K TyFuncCode ⊕ TermF-rest) f
  --              = [ inl ∘ fmap (K TyFuncCode) f , inr ∘ fmap TermF-rest f ]
  --              = [ inl ∘ id , inr ∘ fmap TermF-rest f ]
  -- So [ inl ∘ id , ... ] ∘ inl ⟶ inl ∘ id by case-inl
  -- And inl ∘ id ⟶ inl by id-right
  step case-inl (step id-right done)

fmap-TermF-inr : ∀ {A B} (f : Term A B) →
                 (fmap TermF f ∘ inr) ⟶* (inr ∘ fmap TermF-1 f)
fmap-TermF-inr f = fmap-through-inr (K TyFuncCode) TermF-1 f

fmap-1-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-1 f ∘ inr) ⟶* (inr ∘ fmap TermF-2 f)
fmap-1-inr f = fmap-through-inr (Id ⊗ Id) TermF-2 f

fmap-2-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-2 f ∘ inr) ⟶* (inr ∘ fmap TermF-3 f)
fmap-2-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-3 f

fmap-3-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-3 f ∘ inr) ⟶* (inr ∘ fmap TermF-4 f)
fmap-3-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-4 f

fmap-4-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-4 f ∘ inr) ⟶* (inr ∘ fmap TermF-5 f)
fmap-4-inr f = fmap-through-inr (Id ⊗ Id) TermF-5 f

fmap-5-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-5 f ∘ inr) ⟶* (inr ∘ fmap TermF-6 f)
fmap-5-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-6 f

fmap-6-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-6 f ∘ inr) ⟶* (inr ∘ fmap TermF-7 f)
fmap-6-inr f = fmap-through-inr (K TyFuncCode ⊗ K TyFuncCode) TermF-7 f

fmap-7-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-7 f ∘ inr) ⟶* (inr ∘ fmap TermF-8 f)
fmap-7-inr f = fmap-through-inr (Id ⊗ Id) TermF-8 f

fmap-8-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-8 f ∘ inr) ⟶* (inr ∘ fmap TermF-9 f)
fmap-8-inr f = fmap-through-inr (K TyFuncCode) TermF-9 f

fmap-9-inr : ∀ {A B} (f : Term A B) →
             (fmap TermF-9 f ∘ inr) ⟶* (inr ∘ fmap TermF-10 f)
fmap-9-inr f = fmap-through-inr (K TyFuncCode) TermF-10 f

fmap-10-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-10 f ∘ inr) ⟶* (inr ∘ fmap TermF-11 f)
fmap-10-inr f = fmap-through-inr (K TyFuncCode) TermF-11 f

fmap-11-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-11 f ∘ inr) ⟶* (inr ∘ fmap TermF-12 f)
fmap-11-inr f = fmap-through-inr (K TyFuncCode) TermF-12 f

fmap-12-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-12 f ∘ inr) ⟶* (inr ∘ fmap TermF-13 f)
fmap-12-inr f = fmap-through-inr (K TyFuncCode ⊗ Id) TermF-13 f

fmap-13-inr : ∀ {A B} (f : Term A B) →
              (fmap TermF-13 f ∘ inr) ⟶* (inr ∘ fmap TermF-14 f)
fmap-13-inr f = fmap-through-inr ((K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)) TermF-14 f

------------------------------------------------------------------------
-- fmap distribution through inl (at each level)
------------------------------------------------------------------------

-- Position 2 (fst): after 2 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-2-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-2 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-2-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-3 f

-- Position 3 (snd): after 3 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-3-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-3 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-3-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-4 f

-- Position 5 (inl): after 5 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-5-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-5 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-5-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-6 f

-- Position 6 (inr): after 6 inrs, inl into K TyFuncCode ⊗ K TyFuncCode
fmap-6-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-6 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ K TyFuncCode) f)
fmap-6-inl f = fmap-sum-inl (K TyFuncCode ⊗ K TyFuncCode) TermF-7 f

-- Position 8 (terminal): after 8 inrs, inl into K TyFuncCode
fmap-8-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-8 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-8-inl f = fmap-sum-inl (K TyFuncCode) TermF-9 f

-- Position 9 (initial): after 9 inrs, inl into K TyFuncCode
fmap-9-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-9 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-9-inl f = fmap-sum-inl (K TyFuncCode) TermF-10 f

-- Position 10 (In): after 10 inrs, inl into K TyFuncCode
fmap-10-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-10 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-10-inl f = fmap-sum-inl (K TyFuncCode) TermF-11 f

-- Id⊗Id positions (for recursive cases):
-- Position 1 (comp): after 1 inr, inl into Id ⊗ Id
fmap-1-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-1 f ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) f)
fmap-1-inl f = fmap-sum-inl (Id ⊗ Id) TermF-2 f

-- Position 4 (pair): after 4 inrs, inl into Id ⊗ Id
fmap-4-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-4 f ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) f)
fmap-4-inl f = fmap-sum-inl (Id ⊗ Id) TermF-5 f

-- Position 7 (case): after 7 inrs, inl into Id ⊗ Id
fmap-7-inl : ∀ {A B} (f : Term A B) →
             (fmap TermF-7 f ∘ inl) ⟶* (inl ∘ fmap (Id ⊗ Id) f)
fmap-7-inl f = fmap-sum-inl (Id ⊗ Id) TermF-8 f

-- Position 11 (Out): after 11 inrs, inl into K TyFuncCode
fmap-11-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-11 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode) f)
fmap-11-inl f = fmap-sum-inl (K TyFuncCode) TermF-12 f

-- Position 12 (cata): after 12 inrs, inl into K TyFuncCode ⊗ Id
fmap-12-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-12 f ∘ inl) ⟶* (inl ∘ fmap (K TyFuncCode ⊗ Id) f)
fmap-12-inl f = fmap-sum-inl (K TyFuncCode ⊗ Id) TermF-13 f

-- Curry payload functor: (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)
-- Used at position 13 for the curry constructor
CurryPayloadF : Func
CurryPayloadF = (K TyFuncCode ⊗ K TyFuncCode) ⊗ (K TyFuncCode ⊗ Id)

-- Position 13 (curry): after 13 inrs, inl into curry's type
fmap-13-inl : ∀ {A B} (f : Term A B) →
              (fmap TermF-13 f ∘ inl) ⟶* (inl ∘ fmap CurryPayloadF f)
fmap-13-inl f = fmap-sum-inl CurryPayloadF TermF-14 f
