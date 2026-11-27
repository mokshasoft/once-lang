-- SPIKE: the Knot link (SPIKE-GENERIC-SYNTAX S5, part 1): QUOTATION of the
-- generic syntax into the kernel's own terms, generic in the signature.
--
-- Today the Knot quotes the hand-written `RTm`/`RTy` with one generated
-- clause per former (`Knot/Terms`), and bridges them to `Lib/SynUnq`'s
-- generic trees `STm` with another (`Knot/Unquote`, 2445 generated lines).
-- Here the Spec's syntax IS generic, so the quotation is ONE definition for
-- every signature, and its injectivity and closedness are ONE proof each.
-- A signature supplies only an ENUMERATION of its constructors (a tag per
-- constructor, a decoder back, the round trip): about three lines per former,
-- written once, and no case analysis on pairs of formers.
--
-- The object encoding is `Lib/SynUnq`'s exactly: a node is
-- `con (pair (tag k) payload)`, fields are right-nested `pair`s ending in
-- `unit`, a natural is a numeral, a variable is the variable constructor's
-- node with its index as a tag.

{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong; cong₂; subst; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Scope using ( Cx; ε; _∙; Var; vz; vs )
import DirectedHoTT.Spec.Syntax as S
open import tmp.GenSyn
module tmp.GenSynQuote where

------------------------------------------------------------------------
-- The object-level encoding's pieces (as in `Lib/Sugar`)
------------------------------------------------------------------------

tag : ∀ {Θ} → ℕ → S.RTm Θ
tag zero    = S.fzero
tag (suc k) = S.fsuc (tag k)

num : ∀ {Θ} → ℕ → S.RTm Θ
num zero    = S.nzero
num (suc m) = S.nsuc (num m)

conₗ : ∀ {Θ} → ℕ → S.RTm Θ → S.RTm Θ
conₗ k p = S.con (S.pair (tag k) p)

toℕ : ∀ {Γ} → Var Γ → ℕ
toℕ vz     = zero
toℕ (vs x) = suc (toℕ x)

------------------------------------------------------------------------
-- What a signature supplies: an enumeration of its constructors
------------------------------------------------------------------------

record Enum (Σ : Sig) : Set where
  field
    ix   : ∀ {s} → Con Σ s → ℕ                 -- the constructor's object tag
    cx   : ∀ s → ℕ → Maybe (Con Σ s)           -- tags back to constructors
    rt   : ∀ {s} (c : Con Σ s) → cx s (ix c) ≡ just c
    vix  : ℕ                                   -- the variable constructor's tag
    vfresh : cx (vsort Σ) vix ≡ nothing        -- no constructor of the variable sort has it

------------------------------------------------------------------------
-- THE quotation, for every signature
------------------------------------------------------------------------

module Quote {Σ : Sig} (E : Enum Σ) where
  open Enum E

  ⌜_⌝  : ∀ {s Γ} → Tm Σ s Γ → {Θ : Cx} → S.RTm Θ
  ⌜_⌝ᵃ : ∀ {fs Γ} → Args Σ Γ fs → {Θ : Cx} → S.RTm Θ
  ⌜ var x ⌝      = conₗ vix (S.pair (tag (toℕ x)) S.unit)
  ⌜ con c as ⌝   = conₗ (ix c) ⌜ as ⌝ᵃ
  ⌜ [] ⌝ᵃ        = S.unit
  ⌜ t ∷ʳ as ⌝ᵃ   = S.pair ⌜ t ⌝ ⌜ as ⌝ᵃ
  ⌜ n ∷ⁿ as ⌝ᵃ   = S.pair (num n) ⌜ as ⌝ᵃ

  ----------------------------------------------------------------------
  -- A quotation is CLOSED: substitution leaves it alone
  ----------------------------------------------------------------------

  private
    tag-sub : ∀ {Δ Θ} (σ : S.Sub Δ Θ) k → S.subTm σ (tag {Δ} k) ≡ tag k
    tag-sub σ zero    = refl
    tag-sub σ (suc k) = cong S.fsuc (tag-sub σ k)

    num-sub : ∀ {Δ Θ} (σ : S.Sub Δ Θ) m → S.subTm σ (num {Δ} m) ≡ num m
    num-sub σ zero    = refl
    num-sub σ (suc m) = cong S.nsuc (num-sub σ m)

  ⌜⌝-sub  : ∀ {s Γ Δ Θ} (σ : S.Sub Δ Θ) (t : Tm Σ s Γ) → S.subTm σ (⌜ t ⌝ {Θ = Δ}) ≡ ⌜ t ⌝
  ⌜⌝ᵃ-sub : ∀ {fs Γ Δ Θ} (σ : S.Sub Δ Θ) (as : Args Σ Γ fs) → S.subTm σ (⌜ as ⌝ᵃ {Θ = Δ}) ≡ ⌜ as ⌝ᵃ
  ⌜⌝-sub σ (var x)    = cong₂ (λ a b → S.con (S.pair a (S.pair b S.unit))) (tag-sub σ vix) (tag-sub σ (toℕ x))
  ⌜⌝-sub σ (con c as) = cong₂ (λ a b → S.con (S.pair a b)) (tag-sub σ (ix c)) (⌜⌝ᵃ-sub σ as)
  ⌜⌝ᵃ-sub σ []         = refl
  ⌜⌝ᵃ-sub σ (t ∷ʳ as)  = cong₂ S.pair (⌜⌝-sub σ t) (⌜⌝ᵃ-sub σ as)
  ⌜⌝ᵃ-sub σ (n ∷ⁿ as)  = cong₂ S.pair (num-sub σ n) (⌜⌝ᵃ-sub σ as)

  ----------------------------------------------------------------------
  -- Quotation is INJECTIVE, structurally
  ----------------------------------------------------------------------

  private
    con-inj : ∀ {Θ} {a b : S.RTm Θ} → S.con a ≡ S.con b → a ≡ b
    con-inj refl = refl
    pairˡ : ∀ {Θ} {a b a′ b′ : S.RTm Θ} → S.pair a b ≡ S.pair a′ b′ → a ≡ a′
    pairˡ refl = refl
    pairʳ : ∀ {Θ} {a b a′ b′ : S.RTm Θ} → S.pair a b ≡ S.pair a′ b′ → b ≡ b′
    pairʳ refl = refl
    fsuc-inj : ∀ {Θ} {a b : S.RTm Θ} → S.fsuc a ≡ S.fsuc b → a ≡ b
    fsuc-inj refl = refl
    nsuc-inj : ∀ {Θ} {a b : S.RTm Θ} → S.nsuc a ≡ S.nsuc b → a ≡ b
    nsuc-inj refl = refl

    tag-inj : ∀ {Θ} (k k′ : ℕ) → tag {Θ} k ≡ tag k′ → k ≡ k′
    tag-inj zero    zero     _ = refl
    tag-inj zero    (suc k′) ()
    tag-inj (suc k) zero     ()
    tag-inj (suc k) (suc k′) e = cong suc (tag-inj k k′ (fsuc-inj e))

    num-inj : ∀ {Θ} (m m′ : ℕ) → num {Θ} m ≡ num m′ → m ≡ m′
    num-inj zero    zero     _ = refl
    num-inj zero    (suc m′) ()
    num-inj (suc m) zero     ()
    num-inj (suc m) (suc m′) e = cong suc (num-inj m m′ (nsuc-inj e))

    toℕ-inj : ∀ {Γ} (x y : Var Γ) → toℕ x ≡ toℕ y → x ≡ y
    toℕ-inj vz     vz     _ = refl
    toℕ-inj vz     (vs y) ()
    toℕ-inj (vs x) vz     ()
    toℕ-inj (vs x) (vs y) e = cong vs (toℕ-inj x y (suc-inj e))
      where suc-inj : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
            suc-inj refl = refl

    just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
    just-inj refl = refl

    nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
    nothing≢just ()

    -- the enumeration's tags are injective, by the round trip
    ix-inj : ∀ {s} (c c′ : Con Σ s) → ix c ≡ ix c′ → c ≡ c′
    ix-inj {s} c c′ e = just-inj (trans (sym (rt c)) (trans (cong (cx s) e) (rt c′)))

    -- and no constructor of the variable sort carries the variable's tag
    vix-fresh : ∀ (c : Con Σ (vsort Σ)) → ix c ≡ vix → ⊥
    vix-fresh c e = nothing≢just (trans (sym vfresh) (trans (cong (cx (vsort Σ)) (sym e)) (rt c)))

  ⌜⌝-inj  : ∀ {s Γ Θ} (t u : Tm Σ s Γ) → ⌜ t ⌝ {Θ = Θ} ≡ ⌜ u ⌝ → t ≡ u
  ⌜⌝ᵃ-inj : ∀ {fs Γ Θ} (as bs : Args Σ Γ fs) → ⌜ as ⌝ᵃ {Θ = Θ} ≡ ⌜ bs ⌝ᵃ → as ≡ bs
  ⌜⌝-inj (var x) (var y) e = cong var (toℕ-inj x y (tag-inj _ _ (pairˡ (pairʳ (con-inj e)))))
  ⌜⌝-inj (var x) (con c bs) e = ⊥-elim (vix-fresh c (sym (tag-inj _ _ (pairˡ (con-inj e)))))
    where ⊥-elim : ∀ {A : Set} → ⊥ → A
          ⊥-elim ()
  ⌜⌝-inj (con c as) (var y) e = ⊥-elim (vix-fresh c (tag-inj _ _ (pairˡ (con-inj e))))
    where ⊥-elim : ∀ {A : Set} → ⊥ → A
          ⊥-elim ()
  ⌜⌝-inj (con c as) (con c′ bs) e with ix-inj c c′ (tag-inj _ _ (pairˡ (con-inj e)))
  ... | refl = cong (con c) (⌜⌝ᵃ-inj as bs (pairʳ (con-inj e)))
  ⌜⌝ᵃ-inj [] [] e = refl
  ⌜⌝ᵃ-inj (t ∷ʳ as) (u ∷ʳ bs) e = cong₂ _∷ʳ_ (⌜⌝-inj t u (pairˡ e)) (⌜⌝ᵃ-inj as bs (pairʳ e))
  ⌜⌝ᵃ-inj (n ∷ⁿ as) (m ∷ⁿ bs) e = cong₂ _∷ⁿ_ (num-inj n m (pairˡ e)) (⌜⌝ᵃ-inj as bs (pairʳ e))
