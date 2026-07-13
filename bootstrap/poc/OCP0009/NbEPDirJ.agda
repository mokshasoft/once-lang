------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 1 — `Hom` IS A DIRECTED IDENTITY TYPE (J, no sym)
--
-- The keystone of the directed path (plan §10): Once's transformation type
-- `Hom t u = t ⟶* u` carries the full structure of an IDENTITY TYPE — with
-- direction. Made precise:
--
--   * `refl` is `done`; the ELIMINATOR of `Hom` is J:
--       - `J⟶`    — two-sided directed path induction (structural);
--       - `J-tgt` — path induction BASED AT THE TARGET (structural, because
--         chains cons on the left);
--       - `J-src` — path induction BASED AT THE SOURCE, derived by CHAIN
--         RE-ASSOCIATION (`snoc`), not by symmetry.
--     In Martin-Löf `Id`, the two based J's are interderivable VIA `sym`.
--     Here they are both derivable — but by genuinely different routes,
--     because there is no `sym` to collapse them:
--   * `no-sym` — symmetry is REFUTED, not merely unprovable: a global
--     `Hom t u → Hom u t` would reverse `opt`, contradicting rung 0's
--     `no-way-back`. And the classical derivation of `sym` FROM `J`
--     (motive `P t u p := Hom u t`) blocks exactly at the step case: it
--     needs to invert a single reduction step, which is the one thing a
--     directed step cannot do. J survives losing `sym`; `sym` does not
--     follow from J. That asymmetry is the mathematical content of
--     "directed".
--   * `transport⟶` — directed transport is NOT free (in `Id`-land it falls
--     out of J): it costs exactly STEP-COVARIANCE of the motive. The
--     canonical covariant family is the hom-family itself:
--     `yo : Hom u v → Hom t u → Hom t v` — the covariant Yoneda action is
--     directed transport at its own hom-family.
--   * `J-U` — J with UNIVERSE-VALUED motives (`NbEPDirU.U`): the directed
--     identity type eliminates into the object-language universe, i.e. the
--     eliminator is available INTERNALLY, one level up from rung 1.
--
-- Everything `--safe`, everything over the actual Once IR and its actual
-- rewrite system — no synthetic apparatus. What remains research (rung 3)
-- is making `Hom` a FORMER of a directed kernel with decidable directed
-- conversion; this module settles what its elimination principle is.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirJ where

open import normalizer.Syntax.Types
  using ( Ty; ⊥; ¬_; _≡_; refl; sym; cong; subst )
open import normalizer.Syntax.CCC as C
  using ( Term; _⟶_; _⟶*_; done; step )
open import poc.OCP0009.NbEPDir
  using ( Hom; idH; _∘H_; ∘H-idˡ; B₂; src; tgt; opt; no-way-back )
open import poc.OCP0009.NbEPDirU
  using ( U; El; `⊥; `unit; `prog; `hom; `π )

------------------------------------------------------------------------
-- J, two-sided: directed path induction. `refl ↦ done`.
------------------------------------------------------------------------

J⟶ : ∀ {A B} (P : (t u : Term A B) → Hom t u → Set)
   → (∀ t → P t t idH)
   → (∀ {t u v} (s : t ⟶ u) (p : Hom u v) → P u v p → P t v (step s p))
   → ∀ {t u} (p : Hom t u) → P t u p
J⟶ P prefl pstep done       = prefl _
J⟶ P prefl pstep (step s p) = pstep s p (J⟶ P prefl pstep p)

-- Based at the TARGET: structural, because chains grow at the source.
J-tgt : ∀ {A B} {v : Term A B} (P : ∀ t → Hom t v → Set)
      → P v idH
      → (∀ {t u} (s : t ⟶ u) (p : Hom u v) → P u p → P t (step s p))
      → ∀ {t} (p : Hom t v) → P t p
J-tgt P prefl pstep done       = prefl
J-tgt P prefl pstep (step s p) = pstep s p (J-tgt P prefl pstep p)

------------------------------------------------------------------------
-- Based at the SOURCE: derivable — but only by re-associating the chain
-- (`snoc`), never by reversing it. In `Id`, `J-src` and `J-tgt` are
-- interderivable via `sym`; here each exists on its own terms.
------------------------------------------------------------------------

snoc : ∀ {A B} {t u v : Term A B} → Hom t u → u ⟶ v → Hom t v
snoc done        s = step s done
snoc (step s₀ p) s = step s₀ (snoc p s)

-- Re-association: appending one step at the end, versus consing the rest.
snoc-assoc : ∀ {A B} {t u v w : Term A B}
             (pre : Hom t u) (s : u ⟶ v) (rest : Hom v w) →
             ((step s rest) ∘H pre) ≡ (rest ∘H snoc pre s)
snoc-assoc done         s rest = refl
snoc-assoc (step s₀ pre) s rest = cong (step s₀) (snoc-assoc pre s rest)

J-src : ∀ {A B} {t : Term A B} (P : ∀ u → Hom t u → Set)
      → P t idH
      → (∀ {u v} (p : Hom t u) (s : u ⟶ v) → P u p → P v (snoc p s))
      → ∀ {u} (p : Hom t u) → P u p
J-src {t = t} P prefl psnoc p = go idH p prefl
  where
  go : ∀ {w u} (pre : Hom t w) (rest : Hom w u) → P w pre → P u (rest ∘H pre)
  go pre done          h = subst (P _) (sym (∘H-idˡ pre)) h
  go pre (step s rest) h =
    subst (P _) (sym (snoc-assoc pre s rest))
          (go (snoc pre s) rest (psnoc pre s h))

------------------------------------------------------------------------
-- NO SYM — refuted, and the J-derivation of sym blocked where it must be.
--
-- The classical route `sym = J (λ t u _ → Hom u t) (λ _ → idH) …` needs the
-- step case `Hom v u → Hom v t` given `s : t ⟶ u` — i.e. inverting the
-- single step `s`. A directed step has no inverse; the derivation stops
-- exactly there. And globally, symmetry is FALSE, not just underivable:
------------------------------------------------------------------------

no-sym : ¬ (∀ {A B} {t u : Term A B} → Hom t u → Hom u t)
no-sym symH = no-way-back (symH opt)

------------------------------------------------------------------------
-- Directed transport: not free — it costs STEP-COVARIANCE of the motive.
-- (In `Id`-land, transport falls out of J unconditionally; the freeness of
-- symmetric transport is a luxury of symmetry.)
------------------------------------------------------------------------

transport⟶ : ∀ {A B} (P : Term A B → Set)
           → (∀ {u v} → u ⟶ v → P u → P v)      -- the covariance fee
           → ∀ {t u} → Hom t u → P t → P u
transport⟶ P cov done       x = x
transport⟶ P cov (step s p) x = transport⟶ P cov p (cov s x)

-- The canonical covariant family is the hom-family itself: the covariant
-- Yoneda action IS directed transport at `Hom t —`.
yo : ∀ {A B} {t u v : Term A B} → Hom u v → Hom t u → Hom t v
yo q = transport⟶ (Hom _) (λ s r → snoc r s) q

-- ...and it agrees with composition (sanity, on the running example).
_ : yo opt (idH {t = src}) ≡ opt
_ = refl

------------------------------------------------------------------------
-- J WITH UNIVERSE-VALUED MOTIVES — the eliminator, internally available:
-- the motive lands in the object-language universe of rung 1, so directed
-- induction can state and build INTERNAL types.
------------------------------------------------------------------------

J-U : ∀ {A B} (P : (t u : Term A B) → Hom t u → U)
    → (∀ t → El (P t t idH))
    → (∀ {t u v} (s : t ⟶ u) (p : Hom u v) → El (P u v p) → El (P t v (step s p)))
    → ∀ {t u} (p : Hom t u) → El (P t u p)
J-U P prefl pstep done       = prefl _
J-U P prefl pstep (step s p) = pstep s p (J-U P prefl pstep p)

-- Example: "every transformation out of `src` ends somewhere `tgt`-reachable
-- or is still en route" — internal motives can mention `hom`-codes:
`endpoints : ∀ {A B} (t u : Term A B) → Hom t u → U
`endpoints t u _ = `π (`hom u u) (λ _ → `hom t u)

_ : ∀ {A B} {t u : Term A B} (p : Hom t u) → El (`endpoints t u p)
_ = λ p → J-U `endpoints (λ t _ → idH) (λ s p' ih _ → step s (ih idH)) p
