-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Effects — each grade's monad is a monad, and the
-- morphisms along the order and into `T∞` are monad morphisms
-- (`Spec.Metatheory.Effects`).
--
-- Not `--safe`: equality at `act` is `≡` on finite trees, whose nodes hold
-- continuations, so the laws at `act` use function extensionality
-- (`Once.Postulates`), as HEAD's proof did.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Effects (Σ : Signature) where

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Once.Postulates using (extensionality)
open import Once.Spec.Grade using (Purity; pure; act; eff⁺; eff; _·p_; _⊑π_; ⊑-pure; ⊑-pa; ⊑-pe; ⊑-act; ⊑-ae; ⊑-g; ⊑-ge; ⊑-eff)
open import Once.Spec.Signature using (BTy; void; unit; int; float; _*_; _+_)
open import Once.Spec.Effect Σ
open import Once.Spec.Observation Σ using (Interp; History; events; stepEvents; next; resume)
open import Once.Spec.Metatheory using (Effects)
open import Once.Metatheory.Bisim Σ
open import Once.Metatheory.Erase Σ

open T∞ using (force)
open _≈_ using (force≈)

------------------------------------------------------------------------
-- The finite trees
------------------------------------------------------------------------

T-idʳ : ∀ {X} (m : T X) → (m >>=T returnT) ≡ m
T-idʳ (roll (done x))            = refl
T-idʳ (roll (node (call o a k))) = cong (λ k → roll (node (call o a k))) (extensionality λ b → T-idʳ (k b))

T-assoc : ∀ {X Y Z} (m : T X) (f : X → T Y) (g : Y → T Z) → ((m >>=T f) >>=T g) ≡ (m >>=T λ x → f x >>=T g)
T-assoc (roll (done x))            f g = refl
T-assoc (roll (node (call o a k))) f g = cong (λ k → roll (node (call o a k))) (extensionality λ b → T-assoc (k b) f g)

------------------------------------------------------------------------
-- The laws
------------------------------------------------------------------------

M-identityˡ : ∀ {π} (u : pure ⊑π π) {X Y : Set} (x : X) (k : X → M π Y) → EqM π (bind π (return u x) k) (k x)
M-identityˡ ⊑-pure x k = refl
M-identityˡ ⊑-pa   x k = refl
M-identityˡ ⊑-pe   x k = idˡ x k

M-identityʳ : ∀ {π} (u : pure ⊑π π) {X : Set} (m : M π X) → EqM π (bind π m (return u)) m
M-identityʳ ⊑-pure m = refl
M-identityʳ ⊑-pa   m = T-idʳ m
M-identityʳ ⊑-pe   m = idʳ m

M-assoc : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
        → EqM π (bind π (bind π m f) g) (bind π m (λ x → bind π (f x) g))
M-assoc pure m f g = refl
M-assoc act  m f g = T-assoc m f g
M-assoc eff  m f g = assoc m f g
M-assoc eff⁺ (call⁺ (call o a k)) f g =
  record { force≈ = node≈ λ b →
    ≈-trans (assoc (k b) _ _)
            (≈-bind (≈-refl (k b)) (λ x → ≈-sym (forget⁺-bind (f x) λ y → forget⁺ (g y)))) }

sub-return : ∀ {π π′} (u : pure ⊑π π) (g : π ⊑π π′) (u′ : pure ⊑π π′) {X : Set} (x : X)
           → EqM π′ (sub g (return u x)) (return u′ x)
sub-return ⊑-pure ⊑-pure ⊑-pure x = refl
sub-return ⊑-pure ⊑-pa   ⊑-pa   x = refl
sub-return ⊑-pure ⊑-pe   ⊑-pe   x = ≈-refl (return∞ x)
sub-return ⊑-pa   ⊑-act  ⊑-pa   x = refl
sub-return ⊑-pa   ⊑-ae   ⊑-pe   x = embed-return x
sub-return ⊑-pe   ⊑-eff  ⊑-pe   x = ≈-refl (return∞ x)

sub-bind : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
         → EqM π′ (sub g (bind π m k)) (bind π′ (sub g m) (λ x → sub g (k x)))
sub-bind ⊑-pure m k = refl
sub-bind ⊑-pa   m k = refl
sub-bind ⊑-pe   m k = ≈-sym (idˡ m (λ x → return∞ (k x)))
sub-bind ⊑-act  m k = refl
sub-bind ⊑-ae   m k = embed-bind m k
sub-bind ⊑-g    m k = ≈-refl (forget⁺ (m >>=⁺ λ x → forget⁺ (k x)))
sub-bind ⊑-ge   m k = forget⁺-bind m (λ x → forget⁺ (k x))
sub-bind ⊑-eff  m k = ≈-refl (m >>=∞ k)

------------------------------------------------------------------------
-- The observation
------------------------------------------------------------------------

obs-≈    : ∀ (ι : Interp) (h : History) {X : Set} {m m′ : T∞ X}
         → m ≈ m′ → ∀ n → events ι h m n ≡ events ι h m′ n
obs-≈S   : ∀ (ι : Interp) (h : History) {X : Set} {s s′ : Step X (T∞ X)}
         → StepEq _≈_ s s′ → ∀ n → stepEvents ι h s n ≡ stepEvents ι h s′ n
obs-next : ∀ (ι : Interp) (h : History) {X : Set} (b : BTy) v {k k′ : _ → T∞ X}
         → (∀ r → k r ≈ k′ r) → ∀ n → next ι h (resume b v k) n ≡ next ι h (resume b v k′) n
obs-≈ ι h e zero    = refl
obs-≈ ι h e (suc n) = obs-≈S ι h (force≈ e) n
obs-≈S ι h done≈ n = refl
obs-≈S ι h (node≈ {o} {a} e) n = cong (_ ∷_) (obs-next ι _ _ _ e n)
obs-next ι h void    v e n = refl
obs-next ι h unit    v e n = obs-≈ ι h (e v) n
obs-next ι h int     v e n = obs-≈ ι h (e v) n
obs-next ι h float   v e n = obs-≈ ι h (e v) n
obs-next ι h (a * b) v e n = obs-≈ ι h (e v) n
obs-next ι h (a + b) v e n = obs-≈ ι h (e v) n

obs-return : ∀ (ι : Interp) (h : History) {X : Set} (x : X) n → events ι h (return∞ x) n ≡ []
obs-return ι h x zero    = refl
obs-return ι h x (suc n) = refl

effects : Effects Σ
effects = record
  { M-identityˡ = M-identityˡ
  ; M-identityʳ = M-identityʳ
  ; M-assoc     = M-assoc
  ; sub-return  = sub-return
  ; sub-bind    = sub-bind
  ; toT∞-return = toT∞-return
  ; toT∞-bind   = toT∞-bind
  ; toT∞-bindᵍ  = toT∞-bindᵍ
  ; obs-≈       = obs-≈
  ; obs-return  = obs-return
  }
