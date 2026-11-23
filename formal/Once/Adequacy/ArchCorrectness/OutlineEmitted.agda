-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.OutlineEmitted — the outlined program is an
-- image the arch layer runs (D480, plan 0.146 §5 item 8 c).
--
-- What the arch layer reads of a program (`RunContext.Emitted`) holds of
-- `AllocExpand.outline ks P` when it holds of `P`, every size of `P`'s
-- allocations and frees is in `ks` (each at least one word) and no call of
-- `P`'s names a routine: the start stays at pc 0 alone; the routines' and the
-- called sites' instructions are the image's; a site's call finds its size's
-- routine, `P`'s own calls and code words their targets `d` on; a routine's
-- entry follows the jump over the routines or a return, `P`'s own entries their
-- own guards, `d` on.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Once.Spec.Name using (CanonicalName)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.OutlineEmitted (o : CanonicalName) (FS : FrameSemantics)
  (slot-size : ℕ) (word-eq : frame-word FS ≡ slot-size) where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)
import Data.Nat.Properties
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (LabelId; EntryId; e-fn; e-thunk)
open import Once.CCC.Machine.FrameFree using (ImageI)
open import Once.CCC.Machine.AllocMin using (AllocMinI)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (fetch; find-fn; find-thunk; find-entry)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq using (Emitted; module Emitted; GuardAt)
open import Once.CCC.Codegen.AllocExpand using (alloc-fn; free-fn; site-call; prim-routines; skip; skip-label; outline)
open import Once.CCC.Codegen.AllocOutline {FS} using (SiteView; sv-alloc; sv-free; sv-same; site-view; site-same; NotR; RouI; ri-ae; ri-a; ri-r; ri-fe; ri-f; rou; rou-guard; module Out)

private
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  -- a called site: an allocation's or a free's call, or the instruction itself
  data Called : AbstractInstr → Set where
    c-alloc : ∀ k → Called (instr-alloc-heap k)
    c-free  : ∀ k → Called (instr-free-heap k)
    c-same  : ∀ {i} → site-call i ≡ i → Called i

  called : ∀ i → Called i
  called i = go (site-view i)
    where go : ∀ {j} → SiteView j → Called j
          go (sv-alloc k) = c-alloc k
          go (sv-free k)  = c-free k
          go (sv-same e)  = c-same e

  image-site : ∀ i → ImageI i → ImageI (site-call i)
  image-site i im = go (called i) im
    where go : ∀ {j} → Called j → ImageI j → ImageI (site-call j)
          go (c-alloc k) _  = tt
          go (c-free k)  _  = tt
          go {j} (c-same s) im′ = subst ImageI (sym s) im′

  min-site : ∀ i → AllocMinI i → AllocMinI (site-call i)
  min-site i am = go (called i) am
    where go : ∀ {j} → Called j → AllocMinI j → AllocMinI (site-call j)
          go (c-alloc k) _  = tt
          go (c-free k)  _  = tt
          go {j} (c-same s) am′ = subst AllocMinI (sym s) am′

module _ (ks : List ℕ) (b : ℕ) (T : AbstractTrace) where
  open Out ks b T

  module _ (em : Emitted P)
           (ks-pos : ∀ k → k ∈ ks → 1 ≤ k)
           (sz     : ∀ q k → (fetch T q ≡ just (instr-alloc-heap k)) ⊎ (fetch T q ≡ just (instr-free-heap k)) → k ∈ ks)
           (nc     : ∀ q i f → fetch T q ≡ just i → i ≡ instr-ctrl (c-call-fn f) → NotR (e-fn f))
           where
    private
      module E = Emitted em

      rou-image : ∀ ks′ → All ImageI (prim-routines ks′)
      rou-image []        = []
      rou-image (k ∷ ks′) = tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ rou-image ks′

      rou-min : ∀ ks′ → (∀ k → k ∈ ks′ → 1 ≤ k) → All AllocMinI (prim-routines ks′)
      rou-min []        _ = []
      rou-min (k ∷ ks′) p = tt ∷ p k (Data.List.Relation.Unary.Any.here refl) ∷ tt ∷ tt ∷ p k (Data.List.Relation.Unary.Any.here refl) ∷ tt
                          ∷ rou-min ks′ (λ k′ m → p k′ (Data.List.Relation.Unary.Any.there m))

      tail-all : ∀ {Q : AbstractInstr → Set} → All Q P → All Q T
      tail-all (_ ∷ qs) = qs

      map-all : ∀ {Q : AbstractInstr → Set} → (∀ i → Q i → Q (site-call i)) → ∀ (xs : AbstractTrace) → All Q xs → All Q (map site-call xs)
      map-all f []       []       = []
      map-all f (x ∷ xs) (q ∷ qs) = f x q ∷ map-all f xs qs

      skip-all : ∀ {Q : AbstractInstr → Set} → Q (instr-ctrl (c-jmp skip-label)) → All Q (prim-routines ks) → Q (instr-ctrl (c-label skip-label))
               → All Q (skip ks)
      skip-all qj qr ql = qj ∷ Data.List.Relation.Unary.All.Properties.++⁺ qr (ql ∷ [])

    -- ★ the outlined program is emitted
    emitted : Emitted P′
    emitted = record
      { em-budget = E.em-budget
      ; em-zero   = E.em-zero
      ; em-start  = start
      ; em-image  = tt ∷ Data.List.Relation.Unary.All.Properties.++⁺ (skip-all tt (rou-image ks) tt) (map-all image-site T (tail-all E.em-image))
      ; em-alloc  = tt ∷ Data.List.Relation.Unary.All.Properties.++⁺ (skip-all tt (rou-min ks ks-pos) tt) (map-all min-site T (tail-all E.em-alloc))
      ; em-calls  = calls
      ; em-code   = code
      ; em-guard  = guard
      }
      where
        start : ∀ k b′ → fetch P′ k ≡ just (instr-ctrl (c-start b′)) → k ≡ 0
        start k b′ f = go (where-P′ k _ f)
          where go : WhereP′ k (instr-ctrl (c-start b′)) → k ≡ 0
                go (w-start e _)         = e
                go (w-jmp _ ())
                go (w-rou j _ r)         = ⊥-elim (no-start (rou ks j _ r))
                  where no-start : RouI ks (instr-ctrl (c-start b′)) → ⊥
                        no-start ()
                go (w-lab _ ())
                go (w-own q i′ _ ft ei)  =
                  ⊥-elim (Data.Nat.Properties.1+n≢0 (E.em-start (suc q) b′ (trans ft (cong just (site-same ei (λ f ()))))))

        calls : ∀ k f → fetch P′ k ≡ just (instr-ctrl (c-call-fn f)) → Σ ℕ (λ j → find-fn P′ f ≡ just j)
        calls k f fe = go (where-P′ k _ fe)
          where
            go : WhereP′ k (instr-ctrl (c-call-fn f)) → Σ ℕ (λ j → find-fn P′ f ≡ just j)
            go (w-start _ ())
            go (w-jmp _ ())
            go (w-rou j _ r) = ⊥-elim (no-call (rou ks j _ r))
              where no-call : RouI ks (instr-ctrl (c-call-fn f)) → ⊥
                    no-call ()
            go (w-lab _ ())
            go (w-own q i′ _ ft ei) = site (called i′) ft ei
              where
                site : Called i′ → fetch T q ≡ just i′ → instr-ctrl (c-call-fn f) ≡ site-call i′ → Σ ℕ (λ j → find-fn P′ f ≡ just j)
                site (c-alloc k′) ft′ refl = _ , find-alloc k′ (sz q k′ (inj₁ ft′))
                site (c-free k′)  ft′ refl = _ , find-free k′ (sz q k′ (inj₂ ft′))
                site (c-same s)   ft′ ei′ =
                  let e₀ = trans (sym s) (sym ei′)
                      (j , fj) = E.em-calls (suc q) f (trans ft′ (cong just e₀))
                  in _ , trans (find-entry-out (e-fn f) (nc q i′ f ft′ e₀)) (cong (Data.Maybe.map (d +_)) fj)

        code : ∀ p (ℓ : LabelId) → fetch P′ p ≡ just (instr-load-code-addr ℓ) → Σ ℕ (λ j → find-thunk P′ ℓ ≡ just j)
        code p ℓ fe = go (where-P′ p _ fe)
          where
            go : WhereP′ p (instr-load-code-addr ℓ) → Σ ℕ (λ j → find-thunk P′ ℓ ≡ just j)
            go (w-start _ ())
            go (w-jmp _ ())
            go (w-rou j _ r) = ⊥-elim (no-code (rou ks j _ r))
              where no-code : RouI ks (instr-load-code-addr ℓ) → ⊥
                    no-code ()
            go (w-lab _ ())
            go (w-own q i′ _ ft ei) =
              let e₀ = site-same ei (λ f ())
                  (j , fj) = E.em-code (suc q) ℓ (trans ft (cong just e₀))
              in _ , trans (find-entry-out (e-thunk ℓ) (λ k → (λ ()) , (λ ()))) (cong (Data.Maybe.map (d +_)) fj)

        guard : GuardAt P′
        guard p ℓ bb fe = go (where-P′ p _ fe)
          where
            G : ℕ → Set
            G q = (Σ LabelId (λ m → fetch P′ q ≡ just (instr-ctrl (c-jmp m))))
                  ⊎ (Σ ℕ (λ b′ → fetch P′ q ≡ just (instr-ctrl (c-ret b′))))
                  ⊎ (fetch P′ q ≡ just (instr-ctrl c-leave))
            go : WhereP′ p (instr-ctrl (c-entry ℓ bb)) → Σ ℕ (λ q → (p ≡ suc q) × G q)
            go (w-start _ ())
            go (w-jmp _ ())
            go (w-rou j pj r) = rg (rou-guard ks j ℓ bb r)
              where
                rg : (j ≡ 0) ⊎ Σ ℕ (λ q → (j ≡ suc q) × fetch (prim-routines ks) q ≡ just (instr-ctrl (c-ret 0))) → Σ ℕ (λ q → (p ≡ suc q) × G q)
                rg (inj₁ refl)            = 1 , pj , inj₁ (skip-label , refl)
                rg (inj₂ (q , refl , fr)) = suc (suc q) , pj , inj₂ (inj₁ (0 , rou-at q _ fr))
            go (w-lab _ ())
            go (w-own q i′ pq ft ei) = own (E.em-guard (suc q) ℓ bb (trans ft (cong just (site-same ei (λ f ())))))
              where
                own : Σ ℕ (λ q₀ → (suc q ≡ suc q₀) × ((Σ LabelId (λ m → fetch P q₀ ≡ just (instr-ctrl (c-jmp m))))
                                                       ⊎ (Σ ℕ (λ b′ → fetch P q₀ ≡ just (instr-ctrl (c-ret b′))))
                                                       ⊎ (fetch P q₀ ≡ just (instr-ctrl c-leave))))
                    → Σ ℕ (λ q′ → (p ≡ suc q′) × G q′)
                own (zero , refl , inj₁ (m , ()))
                own (zero , refl , inj₂ (inj₁ (b′ , ())))
                own (zero , refl , inj₂ (inj₂ ()))
                own (suc q₀ , refl , g) =
                  d + suc q₀ , trans pq (+-suc′ d (suc q₀)) , lift g
                  where
                    +-suc′ : ∀ a c → a + suc c ≡ suc (a + c)
                    +-suc′ = Data.Nat.Properties.+-suc
                    at : ∀ {x} → fetch T q₀ ≡ just x → fetch P′ (d + suc q₀) ≡ just (site-call x)
                    at f = trans (fetch-out q₀) (cong (Data.Maybe.map site-call) f)
                    lift : _ → G (d + suc q₀)
                    lift (inj₁ (m , f))          = inj₁ (m , at f)
                    lift (inj₂ (inj₁ (b′ , f))) = inj₂ (inj₁ (b′ , at f))
                    lift (inj₂ (inj₂ f))         = inj₂ (inj₂ (at f))
