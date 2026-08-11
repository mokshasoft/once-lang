------------------------------------------------------------------------
-- Theory.Syntax.CCTB.LocalConfluence
--
-- Local confluence of the full CCTB reduction _⟶full_. Combined with
-- SN (Theory.Syntax.CCTB.SN) and Newman's lemma (Theory.Derived.Newman),
-- this yields full confluence of _⟶full_.
--
-- Rule set (categorically complete via universal properties):
--   β-rules:  fst-pair, snd-pair, eta-pair, id-left, id-right
--   s-rules:  assoc, pair-dist, eta-pair-gen, term-unique
--
-- The β-only _⟶_ (via CCTB-Close instantiation in CCTB.agda) also has
-- constructors named base/∘-congˡ/… in scope from the public open, so
-- we use the qualified module alias `F = full-Closure` to refer to the
-- full-reduction constructors unambiguously.
--
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.CCTB.LocalConfluence where

open import Data.Product
  using (Σ; _,_; proj₁; proj₂) renaming (_×_ to _∧_)

open import Theory.Syntax.StrongCCL.CCTB
module F = full-Closure

------------------------------------------------------------------------
-- Transitive-closure helpers
------------------------------------------------------------------------

⟶full*-trans : ∀ {A B} {t u v : Term A B} →
               t ⟶full* u → u ⟶full* v → t ⟶full* v
⟶full*-trans done     yz = yz
⟶full*-trans (r ∷ xy) yz = r ∷ ⟶full*-trans xy yz

single : ∀ {A B} {t u : Term A B} → t ⟶full u → t ⟶full* u
single r = r ∷ done

⟶full*-∘ˡ : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
            f ⟶full* f' → (f ∘ g) ⟶full* (f' ∘ g)
⟶full*-∘ˡ done     = done
⟶full*-∘ˡ (r ∷ rs) = F.∘-congˡ r ∷ ⟶full*-∘ˡ rs

⟶full*-∘ʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
            g ⟶full* g' → (f ∘ g) ⟶full* (f ∘ g')
⟶full*-∘ʳ done     = done
⟶full*-∘ʳ (r ∷ rs) = F.∘-congʳ r ∷ ⟶full*-∘ʳ rs

⟶full*-⟨,⟩ˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
              f ⟶full* f' → ⟨ f , g ⟩ ⟶full* ⟨ f' , g ⟩
⟶full*-⟨,⟩ˡ done     = done
⟶full*-⟨,⟩ˡ (r ∷ rs) = F.⟨,⟩-congˡ r ∷ ⟶full*-⟨,⟩ˡ rs

⟶full*-⟨,⟩ʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
              g ⟶full* g' → ⟨ f , g ⟩ ⟶full* ⟨ f , g' ⟩
⟶full*-⟨,⟩ʳ done     = done
⟶full*-⟨,⟩ʳ (r ∷ rs) = F.⟨,⟩-congʳ r ∷ ⟶full*-⟨,⟩ʳ rs

⟶full*-∘ : ∀ {A B C} {f f' : Term B C} {g g' : Term A B} →
           f ⟶full* f' → g ⟶full* g' → (f ∘ g) ⟶full* (f' ∘ g')
⟶full*-∘ ff gg = ⟶full*-trans (⟶full*-∘ˡ ff) (⟶full*-∘ʳ gg)

⟶full*-⟨,⟩ : ∀ {A B C} {f f' : Term C A} {g g' : Term C B} →
             f ⟶full* f' → g ⟶full* g' → ⟨ f , g ⟩ ⟶full* ⟨ f' , g' ⟩
⟶full*-⟨,⟩ ff gg = ⟶full*-trans (⟶full*-⟨,⟩ˡ ff) (⟶full*-⟨,⟩ʳ gg)

------------------------------------------------------------------------
-- Joinability
------------------------------------------------------------------------

Joinable : ∀ {A B} (t u : Term A B) → Set
Joinable t u = Σ _ (λ v → (t ⟶full* v) ∧ (u ⟶full* v))

LocalConfluent : Set
LocalConfluent = ∀ {A B} {s t u : Term A B} →
                 s ⟶full t → s ⟶full u → Joinable t u

joinable-refl : ∀ {A B} (t : Term A B) → Joinable t t
joinable-refl t = t , done , done

joinable-symm : ∀ {A B} {t u : Term A B} → Joinable t u → Joinable u t
joinable-symm (v , tv , uv) = v , uv , tv

joinable-∘ˡ : ∀ {A B C} {f f' : Term B C} {g : Term A B} →
              Joinable f f' → Joinable (f ∘ g) (f' ∘ g)
joinable-∘ˡ {g = g} (v , fv , f'v) = v ∘ g , ⟶full*-∘ˡ fv , ⟶full*-∘ˡ f'v

joinable-∘ʳ : ∀ {A B C} {f : Term B C} {g g' : Term A B} →
              Joinable g g' → Joinable (f ∘ g) (f ∘ g')
joinable-∘ʳ {f = f} (v , gv , g'v) = f ∘ v , ⟶full*-∘ʳ gv , ⟶full*-∘ʳ g'v

joinable-⟨,⟩ˡ : ∀ {A B C} {f f' : Term C A} {g : Term C B} →
                Joinable f f' → Joinable ⟨ f , g ⟩ ⟨ f' , g ⟩
joinable-⟨,⟩ˡ {g = g} (v , fv , f'v) =
  ⟨ v , g ⟩ , ⟶full*-⟨,⟩ˡ fv , ⟶full*-⟨,⟩ˡ f'v

joinable-⟨,⟩ʳ : ∀ {A B C} {f : Term C A} {g g' : Term C B} →
                Joinable g g' → Joinable ⟨ f , g ⟩ ⟨ f , g' ⟩
joinable-⟨,⟩ʳ {f = f} (v , gv , g'v) =
  ⟨ f , v ⟩ , ⟶full*-⟨,⟩ʳ gv , ⟶full*-⟨,⟩ʳ g'v

------------------------------------------------------------------------
-- Local confluence proof
------------------------------------------------------------------------

{-# TERMINATING #-}
local-confluent : LocalConfluent

------------------------------------------------------------------------
-- Congruence × Congruence
------------------------------------------------------------------------

-- Same-side: recurse via IH.
local-confluent (F.∘-congˡ r₁)   (F.∘-congˡ r₂)   = joinable-∘ˡ   (local-confluent r₁ r₂)
local-confluent (F.∘-congʳ r₁)   (F.∘-congʳ r₂)   = joinable-∘ʳ   (local-confluent r₁ r₂)
local-confluent (F.⟨,⟩-congˡ r₁) (F.⟨,⟩-congˡ r₂) = joinable-⟨,⟩ˡ (local-confluent r₁ r₂)
local-confluent (F.⟨,⟩-congʳ r₁) (F.⟨,⟩-congʳ r₂) = joinable-⟨,⟩ʳ (local-confluent r₁ r₂)

-- Disjoint sides: commute.
local-confluent (F.∘-congˡ {f' = f'} r₁) (F.∘-congʳ {g' = g'} r₂) =
  f' ∘ g' , single (F.∘-congʳ r₂) , single (F.∘-congˡ r₁)
local-confluent (F.∘-congʳ {g' = g'} r₁) (F.∘-congˡ {f' = f'} r₂) =
  f' ∘ g' , single (F.∘-congˡ r₂) , single (F.∘-congʳ r₁)
local-confluent (F.⟨,⟩-congˡ {f' = f'} r₁) (F.⟨,⟩-congʳ {g' = g'} r₂) =
  ⟨ f' , g' ⟩ , single (F.⟨,⟩-congʳ r₂) , single (F.⟨,⟩-congˡ r₁)
local-confluent (F.⟨,⟩-congʳ {g' = g'} r₁) (F.⟨,⟩-congˡ {f' = f'} r₂) =
  ⟨ f' , g' ⟩ , single (F.⟨,⟩-congˡ r₂) , single (F.⟨,⟩-congʳ r₁)

------------------------------------------------------------------------
-- Base × Base: root-level critical-pair analysis
------------------------------------------------------------------------

local-confluent (F.base r₁) (F.base r₂) = base-base r₁ r₂
  where
  base-base : ∀ {A B} {s t u : Term A B} →
              s ⟶full-rules t → s ⟶full-rules u → Joinable t u

  -- Same rule, same source.
  base-base (β-step fst-pair)  (β-step fst-pair)  = joinable-refl _
  base-base (β-step snd-pair)  (β-step snd-pair)  = joinable-refl _
  base-base (β-step eta-pair)  (β-step eta-pair)  = joinable-refl _
  base-base (β-step id-left)   (β-step id-left)   = joinable-refl _
  base-base (β-step id-right)  (β-step id-right)  = joinable-refl _
  base-base (s-step assoc)     (s-step assoc)     = joinable-refl _
  base-base (s-step pair-dist) (s-step pair-dist) = joinable-refl _
  base-base (s-step eta-pair-gen) (s-step eta-pair-gen) = joinable-refl _
  base-base (s-step term-unique)  (s-step term-unique)  = joinable-refl _

  -- id-left ∩ id-right: s = id ∘ id, both → id.
  base-base (β-step id-left)  (β-step id-right) = joinable-refl _
  base-base (β-step id-right) (β-step id-left)  = joinable-refl _

  -- id-right ∩ assoc: s = (f ∘ g) ∘ id.
  base-base (β-step id-right) (s-step (assoc {f = f} {g = g})) =
    f ∘ g , done , single (F.∘-congʳ (F.base (β-step id-right)))
  base-base (s-step (assoc {f = f} {g = g})) (β-step id-right) =
    f ∘ g , single (F.∘-congʳ (F.base (β-step id-right))) , done

  -- id-right ∩ pair-dist: s = ⟨f, g⟩ ∘ id.
  base-base (β-step id-right) (s-step (pair-dist {f = f} {g = g})) =
    ⟨ f , g ⟩ , done ,
    ⟶full*-trans (single (F.⟨,⟩-congˡ (F.base (β-step id-right))))
                 (single (F.⟨,⟩-congʳ (F.base (β-step id-right))))
  base-base (s-step (pair-dist {f = f} {g = g})) (β-step id-right) =
    ⟨ f , g ⟩ ,
    ⟶full*-trans (single (F.⟨,⟩-congˡ (F.base (β-step id-right))))
                 (single (F.⟨,⟩-congʳ (F.base (β-step id-right)))) ,
    done

  -- id-right ∩ term-unique: s = terminal ∘ id. Both → terminal.
  base-base (β-step id-right)    (s-step term-unique) = joinable-refl _
  base-base (s-step term-unique) (β-step id-right)    = joinable-refl _

------------------------------------------------------------------------
-- Symmetric: congruence × base → base × congruence
------------------------------------------------------------------------

local-confluent (F.∘-congˡ r₁)   (F.base r₂) = joinable-symm (local-confluent (F.base r₂) (F.∘-congˡ r₁))
local-confluent (F.∘-congʳ r₁)   (F.base r₂) = joinable-symm (local-confluent (F.base r₂) (F.∘-congʳ r₁))
local-confluent (F.⟨,⟩-congˡ r₁) (F.base r₂) = joinable-symm (local-confluent (F.base r₂) (F.⟨,⟩-congˡ r₁))
local-confluent (F.⟨,⟩-congʳ r₁) (F.base r₂) = joinable-symm (local-confluent (F.base r₂) (F.⟨,⟩-congʳ r₁))

------------------------------------------------------------------------
-- Base × Congruence: root rule + subterm reduction
--
-- Many combinations are impossible because the base rule pins down a
-- specific atomic in one position (id, fst, snd, terminal), which the
-- congruence cannot reduce. Those cases are absurd via nested `()`.
------------------------------------------------------------------------

-- id-left × ∘-congˡ: congruence on `id`, but id is atomic.
local-confluent (F.base (β-step id-left)) (F.∘-congˡ (F.base (β-step ())))
local-confluent (F.base (β-step id-left)) (F.∘-congˡ (F.base (s-step ())))

-- id-left × ∘-congʳ: s = id ∘ f, cong r : f → f'. Join at f'.
local-confluent (F.base (β-step id-left)) (F.∘-congʳ {g' = f'} r) =
  f' , single r , single (F.base (β-step id-left))

-- id-right × ∘-congˡ: s = f ∘ id, cong r : f → f'. Join at f'.
local-confluent (F.base (β-step id-right)) (F.∘-congˡ {f' = f'} r) =
  f' , single r , single (F.base (β-step id-right))

-- id-right × ∘-congʳ: congruence on `id`, but id is atomic.
local-confluent (F.base (β-step id-right)) (F.∘-congʳ (F.base (β-step ())))
local-confluent (F.base (β-step id-right)) (F.∘-congʳ (F.base (s-step ())))

-- fst-pair × ∘-congˡ: congruence on `fst`, atomic.
local-confluent (F.base (β-step fst-pair)) (F.∘-congˡ (F.base (β-step ())))
local-confluent (F.base (β-step fst-pair)) (F.∘-congˡ (F.base (s-step ())))

-- snd-pair × ∘-congˡ: congruence on `snd`, atomic.
local-confluent (F.base (β-step snd-pair)) (F.∘-congˡ (F.base (β-step ())))
local-confluent (F.base (β-step snd-pair)) (F.∘-congˡ (F.base (s-step ())))

-- term-unique × ∘-congˡ: congruence on `terminal`, atomic.
local-confluent (F.base (s-step term-unique)) (F.∘-congˡ (F.base (β-step ())))
local-confluent (F.base (s-step term-unique)) (F.∘-congˡ (F.base (s-step ())))

-- eta-pair × ⟨,⟩-congˡ / ⟨,⟩-congʳ: congruence on `fst` / `snd`, both atomic.
local-confluent (F.base (β-step eta-pair)) (F.⟨,⟩-congˡ (F.base (β-step ())))
local-confluent (F.base (β-step eta-pair)) (F.⟨,⟩-congˡ (F.base (s-step ())))
local-confluent (F.base (β-step eta-pair)) (F.⟨,⟩-congʳ (F.base (β-step ())))
local-confluent (F.base (β-step eta-pair)) (F.⟨,⟩-congʳ (F.base (s-step ())))

-- fst-pair × ∘-congʳ: s = fst ∘ ⟨h, k⟩, cong r : ⟨h, k⟩ → t'.
local-confluent (F.base (β-step (fst-pair {f = h} {g = k}))) (F.∘-congʳ r) =
  fst-pair-∘-congʳ r
  where
  fst-pair-∘-congʳ : ∀ {t'} → ⟨ h , k ⟩ ⟶full t' → Joinable h (fst ∘ t')
  -- r = eta-pair (h=fst, k=snd, t'=id).
  fst-pair-∘-congʳ (F.base (β-step eta-pair)) =
    fst , done , single (F.base (β-step id-right))
  -- r = eta-pair-gen (h = fst ∘ H, k = snd ∘ H, t' = H for some H).
  fst-pair-∘-congʳ (F.base (s-step (eta-pair-gen {h = H}))) =
    fst ∘ H , done , done
  -- r = ⟨,⟩-congˡ r' (r' : h → h'), t' = ⟨h', k⟩.
  fst-pair-∘-congʳ (F.⟨,⟩-congˡ r') =
    _ , single r' , single (F.base (β-step fst-pair))
  -- r = ⟨,⟩-congʳ r' (r' : k → k'), t' = ⟨h, k'⟩.
  fst-pair-∘-congʳ (F.⟨,⟩-congʳ r') =
    _ , done , single (F.base (β-step fst-pair))

-- snd-pair × ∘-congʳ: analogous.
local-confluent (F.base (β-step (snd-pair {f = h} {g = k}))) (F.∘-congʳ r) =
  snd-pair-∘-congʳ r
  where
  snd-pair-∘-congʳ : ∀ {t'} → ⟨ h , k ⟩ ⟶full t' → Joinable k (snd ∘ t')
  snd-pair-∘-congʳ (F.base (β-step eta-pair)) =
    snd , done , single (F.base (β-step id-right))
  snd-pair-∘-congʳ (F.base (s-step (eta-pair-gen {h = H}))) =
    snd ∘ H , done , done
  snd-pair-∘-congʳ (F.⟨,⟩-congˡ r') =
    _ , done , single (F.base (β-step snd-pair))
  snd-pair-∘-congʳ (F.⟨,⟩-congʳ r') =
    _ , single r' , single (F.base (β-step snd-pair))

-- assoc × ∘-congˡ: s = (f ∘ g) ∘ h, cong r : f ∘ g → t'.
local-confluent (F.base (s-step (assoc {f = f} {g = g} {h = h}))) (F.∘-congˡ r) =
  assoc-∘-congˡ r
  where
  assoc-∘-congˡ : ∀ {t'} → (f ∘ g) ⟶full t' →
                  Joinable (f ∘ (g ∘ h)) (t' ∘ h)
  -- r = base rule at root of (f ∘ g):
  assoc-∘-congˡ (F.base (β-step id-left))   =
    -- f = id, t' = g. Path 1: f ∘ (g ∘ h) = id ∘ (g ∘ h) → g ∘ h. Path 2: g ∘ h.
    _ , single (F.base (β-step id-left)) , done
  assoc-∘-congˡ (F.base (β-step id-right))  =
    -- g = id, t' = f. Path 1: f ∘ (id ∘ h) → f ∘ h (via ∘-congʳ id-left). Path 2: f ∘ h.
    _ , single (F.∘-congʳ (F.base (β-step id-left))) , done
  assoc-∘-congˡ (F.base (β-step (fst-pair {f = a} {g = b}))) =
    -- f = fst, g = ⟨a, b⟩, t' = a.
    -- Path 1: fst ∘ (⟨a, b⟩ ∘ h) →pair-dist fst ∘ ⟨a ∘ h, b ∘ h⟩ →fst-pair a ∘ h.
    -- Path 2: a ∘ h.
    _ ,
    ⟶full*-trans (single (F.∘-congʳ (F.base (s-step pair-dist))))
                 (single (F.base (β-step fst-pair))) ,
    done
  assoc-∘-congˡ (F.base (β-step (snd-pair {f = a} {g = b}))) =
    _ ,
    ⟶full*-trans (single (F.∘-congʳ (F.base (s-step pair-dist))))
                 (single (F.base (β-step snd-pair))) ,
    done
  assoc-∘-congˡ (F.base (s-step (assoc {f = a} {g = b} {h = c}))) =
    -- f = a ∘ b, g = c, t' = a ∘ (b ∘ c).
    -- Path 1: (a ∘ b) ∘ (c ∘ h) →assoc a ∘ (b ∘ (c ∘ h)).
    -- Path 2: (a ∘ (b ∘ c)) ∘ h →assoc a ∘ ((b ∘ c) ∘ h) →∘-congʳ assoc a ∘ (b ∘ (c ∘ h)).
    _ ,
    single (F.base (s-step assoc)) ,
    ⟶full*-trans (single (F.base (s-step assoc)))
                 (single (F.∘-congʳ (F.base (s-step assoc))))
  assoc-∘-congˡ (F.base (s-step (pair-dist {f = a} {g = b}))) =
    -- f = ⟨a, b⟩, t' = ⟨a ∘ g, b ∘ g⟩.
    -- Path 1: ⟨a, b⟩ ∘ (g ∘ h) →pair-dist ⟨a ∘ (g ∘ h), b ∘ (g ∘ h)⟩.
    -- Path 2: ⟨a ∘ g, b ∘ g⟩ ∘ h →pair-dist ⟨(a ∘ g) ∘ h, (b ∘ g) ∘ h⟩
    --       →⟨,⟩-cong (assoc on both) ⟨a ∘ (g ∘ h), b ∘ (g ∘ h)⟩.
    _ ,
    single (F.base (s-step pair-dist)) ,
    ⟶full*-trans (single (F.base (s-step pair-dist)))
                 (⟶full*-trans (single (F.⟨,⟩-congˡ (F.base (s-step assoc))))
                               (single (F.⟨,⟩-congʳ (F.base (s-step assoc)))))
  assoc-∘-congˡ (F.base (s-step (term-unique {f = f'}))) =
    -- f = terminal, g = f' (arbitrary), t' = terminal.
    -- Path 1: terminal ∘ (f' ∘ h) →term-unique terminal.
    -- Path 2: terminal ∘ h →term-unique terminal.
    _ , single (F.base (s-step term-unique)) , single (F.base (s-step term-unique))
  -- r = cong inside (f ∘ g):
  assoc-∘-congˡ (F.∘-congˡ {f' = f'} r') =
    -- f → f'. Path 1: f ∘ (g ∘ h) →∘-congˡ f' ∘ (g ∘ h). Path 2: (f' ∘ g) ∘ h →assoc f' ∘ (g ∘ h).
    _ , single (F.∘-congˡ r') , single (F.base (s-step assoc))
  assoc-∘-congˡ (F.∘-congʳ {g' = g'} r') =
    -- g → g'. Similar.
    _ , single (F.∘-congʳ (F.∘-congˡ r')) , single (F.base (s-step assoc))

-- assoc × ∘-congʳ: s = (f ∘ g) ∘ h, cong r : h → h'.
local-confluent (F.base (s-step (assoc {f = f} {g = g} {h = h}))) (F.∘-congʳ {g' = h'} r) =
  f ∘ (g ∘ h') ,
  single (F.∘-congʳ (F.∘-congʳ r)) ,
  single (F.base (s-step assoc))

-- pair-dist × ∘-congˡ: s = ⟨f, g⟩ ∘ h, cong r : ⟨f, g⟩ → t'.
local-confluent (F.base (s-step (pair-dist {f = f} {g = g} {h = h}))) (F.∘-congˡ r) =
  pair-dist-∘-congˡ r
  where
  pair-dist-∘-congˡ : ∀ {t'} → ⟨ f , g ⟩ ⟶full t' →
                      Joinable ⟨ f ∘ h , g ∘ h ⟩ (t' ∘ h)
  -- r = eta-pair at root: f = fst, g = snd, t' = id. Then t' ∘ h = id ∘ h → h.
  -- Path 1: ⟨fst ∘ h, snd ∘ h⟩ →eta-pair-gen h.
  pair-dist-∘-congˡ (F.base (β-step eta-pair)) =
    h ,
    single (F.base (s-step eta-pair-gen)) ,
    single (F.base (β-step id-left))
  -- r = eta-pair-gen at root: f = fst ∘ H, g = snd ∘ H, t' = H.
  -- Path 1: ⟨(fst ∘ H) ∘ h, (snd ∘ H) ∘ h⟩ → ⟨fst ∘ (H ∘ h), snd ∘ (H ∘ h)⟩ → H ∘ h.
  -- Path 2: H ∘ h.
  pair-dist-∘-congˡ (F.base (s-step (eta-pair-gen {h = H}))) =
    H ∘ h ,
    ⟶full*-trans (⟶full*-trans (single (F.⟨,⟩-congˡ (F.base (s-step assoc))))
                                (single (F.⟨,⟩-congʳ (F.base (s-step assoc)))))
                 (single (F.base (s-step eta-pair-gen))) ,
    done
  pair-dist-∘-congˡ (F.⟨,⟩-congˡ r') =
    _ , single (F.⟨,⟩-congˡ (F.∘-congˡ r')) , single (F.base (s-step pair-dist))
  pair-dist-∘-congˡ (F.⟨,⟩-congʳ r') =
    _ , single (F.⟨,⟩-congʳ (F.∘-congˡ r')) , single (F.base (s-step pair-dist))

-- pair-dist × ∘-congʳ: s = ⟨f, g⟩ ∘ h, cong r : h → h'.
local-confluent (F.base (s-step (pair-dist {f = f} {g = g} {h = h}))) (F.∘-congʳ {g' = h'} r) =
  ⟨ f ∘ h' , g ∘ h' ⟩ ,
  ⟶full*-trans (single (F.⟨,⟩-congˡ (F.∘-congʳ r)))
               (single (F.⟨,⟩-congʳ (F.∘-congʳ r))) ,
  single (F.base (s-step pair-dist))

-- eta-pair-gen × ⟨,⟩-congˡ: s = ⟨fst ∘ h, snd ∘ h⟩, cong r : fst ∘ h → t'.
local-confluent (F.base (s-step (eta-pair-gen {h = h}))) (F.⟨,⟩-congˡ r) =
  eta-pair-gen-⟨,⟩-congˡ r
  where
  eta-pair-gen-⟨,⟩-congˡ : ∀ {t'} → (fst ∘ h) ⟶full t' → Joinable h ⟨ t' , snd ∘ h ⟩
  -- r = base rule at root of (fst ∘ h):
  eta-pair-gen-⟨,⟩-congˡ (F.base (β-step id-right)) =
    -- h = id, t' = fst. s = ⟨fst ∘ id, snd ∘ id⟩ after cong: ⟨fst, snd ∘ id⟩.
    -- Actually: eta-pair-gen with h=id gives id. So base path: id.
    -- Cong ⟨,⟩-congˡ (id-right) makes it ⟨fst, snd ∘ id⟩. eta-pair-gen no longer applies directly.
    -- Need: ⟨fst, snd ∘ id⟩ → ⟨fst, snd⟩ (via ⟨,⟩-congʳ id-right) → id (via eta-pair).
    id ,
    done ,
    ⟶full*-trans (single (F.⟨,⟩-congʳ (F.base (β-step id-right))))
                 (single (F.base (β-step eta-pair)))
  eta-pair-gen-⟨,⟩-congˡ (F.base (β-step (fst-pair {f = a} {g = b}))) =
    -- h = ⟨a, b⟩, t' = a. s = ⟨fst ∘ ⟨a, b⟩, snd ∘ ⟨a, b⟩⟩ after cong: ⟨a, snd ∘ ⟨a, b⟩⟩.
    -- base path: ⟨a, b⟩.
    -- cong path: ⟨a, snd ∘ ⟨a, b⟩⟩ → (via ⟨,⟩-congʳ snd-pair) ⟨a, b⟩.
    ⟨ a , b ⟩ ,
    done ,
    single (F.⟨,⟩-congʳ (F.base (β-step snd-pair)))
  -- r = cong inside (fst ∘ h):
  -- ∘-congˡ would reduce fst, but fst is atomic (no rule applies).
  eta-pair-gen-⟨,⟩-congˡ (F.∘-congˡ (F.base (β-step ())))
  eta-pair-gen-⟨,⟩-congˡ (F.∘-congˡ (F.base (s-step ())))
  eta-pair-gen-⟨,⟩-congˡ (F.∘-congʳ {g' = h'} r') =
    -- h → h'. Path 1: eta-pair-gen → h → h' via r'. Path 2: ⟨fst ∘ h', snd ∘ h⟩ →⟨,⟩-congʳ ⟨fst ∘ h', snd ∘ h'⟩ →eta-pair-gen h'.
    _ ,
    single r' ,
    ⟶full*-trans (single (F.⟨,⟩-congʳ (F.∘-congʳ r')))
                 (single (F.base (s-step eta-pair-gen)))

-- eta-pair-gen × ⟨,⟩-congʳ: s = ⟨fst ∘ h, snd ∘ h⟩, cong r : snd ∘ h → t'.
local-confluent (F.base (s-step (eta-pair-gen {h = h}))) (F.⟨,⟩-congʳ r) =
  eta-pair-gen-⟨,⟩-congʳ r
  where
  eta-pair-gen-⟨,⟩-congʳ : ∀ {t'} → (snd ∘ h) ⟶full t' → Joinable h ⟨ fst ∘ h , t' ⟩
  eta-pair-gen-⟨,⟩-congʳ (F.base (β-step id-right)) =
    id ,
    done ,
    ⟶full*-trans (single (F.⟨,⟩-congˡ (F.base (β-step id-right))))
                 (single (F.base (β-step eta-pair)))
  eta-pair-gen-⟨,⟩-congʳ (F.base (β-step (snd-pair {f = a} {g = b}))) =
    ⟨ a , b ⟩ ,
    done ,
    single (F.⟨,⟩-congˡ (F.base (β-step fst-pair)))
  eta-pair-gen-⟨,⟩-congʳ (F.∘-congˡ (F.base (β-step ())))
  eta-pair-gen-⟨,⟩-congʳ (F.∘-congˡ (F.base (s-step ())))
  eta-pair-gen-⟨,⟩-congʳ (F.∘-congʳ {g' = h'} r') =
    _ ,
    single r' ,
    ⟶full*-trans (single (F.⟨,⟩-congˡ (F.∘-congʳ r')))
                 (single (F.base (s-step eta-pair-gen)))

-- term-unique × ∘-congʳ: s = terminal ∘ f, cong r : f → f'.
local-confluent (F.base (s-step (term-unique {f = f}))) (F.∘-congʳ {g' = f'} r) =
  terminal , done , single (F.base (s-step term-unique))
