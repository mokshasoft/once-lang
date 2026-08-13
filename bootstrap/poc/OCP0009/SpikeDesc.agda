------------------------------------------------------------------------
-- OCP-0009 — ★ THE GATE FOR THE INDUCTIVE-TYPES AXIS.
--
-- `SCOPE-INDUCTIVE.md` §3: do NOT start by touching the kernel.  The whole
-- ~2 kloc cascade hinges on one question, and it can be asked in isolation:
--
--   ⇒ can the LOGICAL RELATION be defined by induction on a DESCRIPTION,
--     and does the fundamental theorem's case for the GENERIC FOLD go
--     through?
--
-- ⚠ WHY THIS IS A FAITHFUL PROXY DESPITE HAVING NO TERM LANGUAGE.  The
--   kernel's `NbEPDirDBLR` is itself written in Agda, so it faces Agda's
--   positivity and termination checkers on exactly these shapes.  What
--   could kill the axis is not the object-language semantics — it is Agda
--   refusing the NESTED definition, and that refusal (or not) shows up at
--   three constructors just as it would at `RTm`'s twenty-five.
--
-- FOUR QUESTIONS, in dependency order:
--   Q1  does `μ D` pass POSITIVITY, given `⟦_⟧` is a function?
--   Q2  does the generic `fold` pass TERMINATION?
--   Q3  ★ does the predicate lifting `Lift` — a function by recursion on
--       the description — survive being used NESTED inside the data
--       declaration of the relation itself?
--   Q4  ★★ does `fund`'s fold case go through, i.e. does the IH ARRIVE at
--       every recursive position?
--
-- Self-contained: no imports, so the file is the evidence.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeDesc where

data ⊤ : Set where
  tt : ⊤

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

------------------------------------------------------------------------
-- THE UNIVERSE.  Three constructors, which is enough to encode ℕ and
-- binary trees — i.e. enough for a recursive position and a choice.
------------------------------------------------------------------------

data Desc : Set where
  ι : Desc              -- no more fields
  ρ : Desc → Desc       -- a RECURSIVE field, then more
  δ : Desc → Desc → Desc -- a CHOICE of two shapes

⟦_⟧ : Desc → Set → Set
⟦ ι ⟧     X = ⊤
⟦ ρ D ⟧   X = X × ⟦ D ⟧ X
⟦ δ D E ⟧ X = ⟦ D ⟧ X ⊎ ⟦ E ⟧ X

-- ★ Q1 — POSITIVITY.  `⟦ D ⟧` is a FUNCTION, so the checker has to unfold
--   it to see `μ D` occurs strictly positively.
data μ (D : Desc) : Set where
  con : ⟦ D ⟧ (μ D) → μ D

------------------------------------------------------------------------
-- ★ Q2 — the generic FOLD, and its termination.
--
-- ⚠ Written MUTUALLY on purpose.  The one-liner
--   `fold f (con xs) = f (map D (fold f) xs)` passes `fold f` as a
--   function argument, and the checker cannot then see that it is only
--   ever applied to subterms.  Splitting the map into the mutual block
--   puts the recursive call on a visible subterm.
------------------------------------------------------------------------

mutual
  fold : {D : Desc} {X : Set} → (⟦ D ⟧ X → X) → μ D → X
  fold {D} f (con xs) = f (foldMap D f xs)

  foldMap : {D : Desc} (E : Desc) {X : Set} → (⟦ D ⟧ X → X) →
            ⟦ E ⟧ (μ D) → ⟦ E ⟧ X
  foldMap ι       f tt      = tt
  foldMap (ρ E)   f (x , r) = fold f x , foldMap E f r
  foldMap (δ E F) f (inl l) = inl (foldMap E f l)
  foldMap (δ E F) f (inr r) = inr (foldMap F f r)

------------------------------------------------------------------------
-- ★★ Q3 — THE LOGICAL RELATION.
--
-- `Lift` is the predicate lifting along a description: "every recursive
-- field satisfies P".  It is a FUNCTION by recursion on the description,
-- and `MuMem` then uses it NESTED, inside its own data declaration.
--
-- ⚠ THIS IS THE GATE.  It is the shape `NbEPDirDBLR`'s `NatMem` would
--   generalise to: `NatMem` has `nm-zero`/`nm-suc` spelled out because ℕ
--   has two constructors; at `μ D` the constructor cases ARE the
--   description, so the relation must be defined by recursion on it.
------------------------------------------------------------------------

Lift : (E : Desc) {X : Set} → (X → Set) → ⟦ E ⟧ X → Set
Lift ι       P tt      = ⊤
Lift (ρ E)   P (x , r) = P x × Lift E P r
Lift (δ E F) P (inl l) = Lift E P l
Lift (δ E F) P (inr r) = Lift F P r

data MuMem (D : Desc) : μ D → Set where
  mm-con : {xs : ⟦ D ⟧ (μ D)} → Lift D (MuMem D) xs → MuMem D (con xs)

------------------------------------------------------------------------
-- the fundamental theorem's EASY half: every element is in the relation.
------------------------------------------------------------------------

mutual
  fundμ : {D : Desc} (t : μ D) → MuMem D t
  fundμ (con xs) = mm-con (fundMap _ xs)

  fundMap : {D : Desc} (E : Desc) (xs : ⟦ E ⟧ (μ D)) → Lift E (MuMem D) xs
  fundMap ι       tt      = tt
  fundMap (ρ E)   (x , r) = fundμ x , fundMap E r
  fundMap (δ E F) (inl l) = fundMap E l
  fundMap (δ E F) (inr r) = fundMap F r

------------------------------------------------------------------------
-- ★★★ Q4 — `fund`'s FOLD CASE.
--
-- The shape the kernel needs: if the algebra takes the lifted predicate to
-- the predicate, then the fold lands in the predicate — for every element
-- of the relation.  ⚠ The whole question is whether the IH ARRIVES at each
-- recursive position, which is what `Lift`'s `ρ` case has to deliver.
------------------------------------------------------------------------

mutual
  foldPres : {D : Desc} {X : Set} {Q : X → Set} (f : ⟦ D ⟧ X → X) →
             ((xs : ⟦ D ⟧ X) → Lift D Q xs → Q (f xs)) →
             (t : μ D) → MuMem D t → Q (fold f t)
  foldPres {D} f alg (con xs) (mm-con m) =
    alg (foldMap D f xs) (foldPresMap D f alg xs m)

  foldPresMap : {D : Desc} (E : Desc) {X : Set} {Q : X → Set}
                (f : ⟦ D ⟧ X → X) →
                ((xs : ⟦ D ⟧ X) → Lift D Q xs → Q (f xs)) →
                (xs : ⟦ E ⟧ (μ D)) → Lift E (MuMem D) xs →
                Lift E Q (foldMap E f xs)
  foldPresMap ι       f alg tt      tt      = tt
  foldPresMap (ρ E)   f alg (x , r) (p , m) =
    foldPres f alg x p , foldPresMap E f alg r m
  foldPresMap (δ E F) f alg (inl l) m = foldPresMap E f alg l m
  foldPresMap (δ E F) f alg (inr r) m = foldPresMap F f alg r m

------------------------------------------------------------------------
-- ★ A CONCRETE INSTANCE, so none of the above is vacuous: ℕ as a
--   description, with `sz` as a fold — which is the acceptance test
--   `ARCHITECTURE.md` names (`sz` definable by the fold).
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

NatD : Desc
NatD = δ ι (ρ ι)

ze : μ NatD
ze = con (inl tt)

su : μ NatD → μ NatD
su n = con (inr (n , tt))

-- `sz` by the GENERIC fold — no bespoke recursor
szAlg : ⟦ NatD ⟧ Nat → Nat
szAlg (inl tt)      = zero
szAlg (inr (n , _)) = suc n

sz : μ NatD → Nat
sz = fold szAlg

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- ★ and it COMPUTES
sz-2 : sz (su (su ze)) ≡ suc (suc zero)
sz-2 = refl

-- ★★ and the generic `foldPres` instantiates: every `sz` is a `Nat`,
--    proved once for all descriptions rather than per datatype.
always : Nat → Set
always _ = ⊤

sz-total : (t : μ NatD) → always (sz t)
sz-total t = foldPres szAlg (λ _ _ → tt) t (fundμ t)
