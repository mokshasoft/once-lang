------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 10 — the GENERAL directed dependent Π (the END)
--
-- Case (b): `Π⁺ A B` for a CONTRAVARIANT domain `A : Ty⁻ ⌊𝒞⌋` and a motive
-- `B : Ty⁺ (⌊𝒞⌋ ▷⁻ A)` over the OP-Grothendieck. Where the representable Π
-- (`NbEPDirPi`) collapsed by Yoneda, the general one is a genuine END — but
-- the FUTURE-CONE presentation makes it tractable, exactly as the pattern
-- predicted:
--
--   * `_▷⁻_`   — the op-Grothendieck (morphisms carry a CONTRAVARIANT proof);
--   * `Πfib`   — the fibre: a record `{ ap ; coh }`, where `ap` indexes values
--                by morphisms OUT of `x` (`h : x ⇒ y`) and `coh` is the WEDGE
--                (the end's naturality). Indexing by out-morphisms is Yoneda's
--                trick: it makes the functor action PRE-COMPOSITION;
--   * `Π⁺`     — a genuine `Ty⁺ ⌊𝒞⌋`. `act f g = λ y h a → ap g y (f⨾h) a`
--                touches NO fibre-transport, so `actid`/`act⨾` fall to
--                `unitˡ`/`assoc` under `funext`; the wedge is preserved by
--                `assoc` + `g.coh`. The record laws close because `CohT` is a
--                PROPOSITION (`funext` + `uip`) — the transport never needs
--                computing.
--
-- Needs `𝒞 : Cat` (the base must be lawful — `Π`'s action uses `unitˡ`/`assoc`,
-- unlike `Σ⁺`/`×⁺`). `funext` threaded. The `coh` field is where the
-- naturality/liveness lives — the dependent-Π face of the `Ana`/codata frontier.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirPiG where

open import normalizer.Syntax.Types
  using ( _≡_; refl; trans; cong; subst; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Cat; ⌊_⌋; Ty⁺; Ty⁻; Tm )
open import poc.OCP0009.NbEPDirSig using ( uip )

------------------------------------------------------------------------
-- The op-Grothendieck comprehension (contravariant domain).
------------------------------------------------------------------------

_▷⁻_ : (Γ : Ctx) → Ty⁻ Γ → Ctx
Γ ▷⁻ A = record
  { Ob  = Σ Ob A.fam
  ; _⇒_ = λ p q → Σ (fst p ⇒ fst q) (λ h → A.act h (snd q) ≡ snd p)
  ; idₒ = idₒ , A.actid _
  ; _⨾_ = λ { (f , ef) (g , eg) →
              (f ⨾ g) , trans (A.act⨾ f g _) (trans (cong (A.act f) eg) ef) } }
  where open Ctx Γ ; module A = Ty⁻ A

------------------------------------------------------------------------
-- The fibre of `Π`: a future-cone family with a wedge.
------------------------------------------------------------------------

record Πfib {Γ : Ctx} (A : Ty⁻ Γ) (B : Ty⁺ (Γ ▷⁻ A)) (x : Ctx.Ob Γ) : Set where
  open Ctx Γ
  module A = Ty⁻ A ; module B = Ty⁺ B
  field
    ap  : (y : Ob) (h : x ⇒ y) (a : A.fam y) → B.fam (y , a)
    coh : (y z : Ob) (h : x ⇒ y) (k : y ⇒ z) (a : A.fam z) →
          B.act (k , refl) (ap y h (A.act k a)) ≡ ap z (h ⨾ k) a

-- Application (the eliminator): evaluate the future-cone at the identity.
-- `app g a = ap g x idₒ a` — the value "here" (`h = idₒ`).
app : ∀ {Γ : Ctx} {A : Ty⁻ Γ} {B : Ty⁺ (Γ ▷⁻ A)} {x : Ctx.Ob Γ} →
      Πfib A B x → (a : Ty⁻.fam A x) → Ty⁺.fam B (x , a)
app {Γ} g a = Πfib.ap g _ (Ctx.idₒ Γ) a

------------------------------------------------------------------------
-- The directed dependent product, over a lawful base, given funext.
------------------------------------------------------------------------

module _ (funext : ∀ {S : Set} {T : S → Set} {f g : (s : S) → T s} →
                   (∀ s → f s ≡ g s) → f ≡ g) where

  module _ (𝒞 : Cat) (A : Ty⁻ ⌊ 𝒞 ⌋) (B : Ty⁺ (⌊ 𝒞 ⌋ ▷⁻ A)) where
    private
      module 𝒞 = Cat 𝒞
      module A = Ty⁻ A ; module B = Ty⁺ B
    open 𝒞 using ( Ob; _⇒_; idₒ; _⨾_; unitˡ; assoc )

    APT : Ob → Set
    APT x = (y : Ob) (h : x ⇒ y) (a : A.fam y) → B.fam (y , a)

    CohT : (x : Ob) → APT x → Set
    CohT x ap = (y z : Ob) (h : x ⇒ y) (k : y ⇒ z) (a : A.fam z) →
                B.act (k , refl) (ap y h (A.act k a)) ≡ ap z (h ⨾ k) a

    mk : ∀ {x} (ap : APT x) → CohT x ap → Πfib A B x
    mk ap coh = record { ap = ap ; coh = coh }

    -- The action is pre-composition; the wedge is preserved by `assoc`.
    act : ∀ {x y} → x ⇒ y → Πfib A B x → Πfib A B y
    act f g = mk (λ y h a → Πfib.ap g y (f ⨾ h) a)
                 (λ y z h k a →
                    trans (Πfib.coh g y z (f ⨾ h) k a)
                          (cong (λ m → Πfib.ap g z m a) (assoc f h k)))

    -- `CohT` is a proposition (its values are `Set`-equality proofs).
    CohT-prop : ∀ {x} (ap : APT x) (c d : CohT x ap) → c ≡ d
    CohT-prop ap c d =
      funext (λ y → funext (λ z → funext (λ h → funext (λ k → funext (λ a →
        uip (c y z h k a) (d y z h k a))))))

    -- Fibre equality from an `ap`-equality alone (the `coh` field is a prop).
    Πfib-≡ : ∀ {x} (p q : Πfib A B x) → Πfib.ap p ≡ Πfib.ap q → p ≡ q
    Πfib-≡ p q e =
      go (Πfib.ap p) (Πfib.ap q) (Πfib.coh p) (Πfib.coh q) e
         (CohT-prop (Πfib.ap q) (subst (CohT _) e (Πfib.coh p)) (Πfib.coh q))
      where
      go : ∀ {x} (ap ap' : APT x) (coh : CohT x ap) (coh' : CohT x ap')
           (e : ap ≡ ap') → subst (CohT x) e coh ≡ coh' → mk ap coh ≡ mk ap' coh'
      go ap .ap coh .coh refl refl = refl

    actid : ∀ {x} (g : Πfib A B x) → act idₒ g ≡ g
    actid g =
      Πfib-≡ (act idₒ g) g
        (funext (λ y → funext (λ h → funext (λ a →
           cong (λ hh → Πfib.ap g y hh a) (unitˡ h)))))

    act⨾ : ∀ {x y z} (f : x ⇒ y) (g : y ⇒ z) (p : Πfib A B x) →
           act (f ⨾ g) p ≡ act g (act f p)
    act⨾ f g p =
      Πfib-≡ (act (f ⨾ g) p) (act g (act f p))
        (funext (λ y → funext (λ h → funext (λ a →
           cong (λ hh → Πfib.ap p y hh a) (assoc f g h)))))

    Π⁺ : Ty⁺ ⌊ 𝒞 ⌋
    Π⁺ = record { fam = Πfib A B ; act = act ; actid = actid ; act⨾ = act⨾ }

    ----------------------------------------------------------------------
    -- Introduction, and the β rule.
    --
    -- `lam` sends a section `b : Tm (⌊𝒞⌋ ▷⁻ A) B` to the future-cone family
    -- `λ y h a → b(y,a)` (constant in the path `h`) — and its wedge (`coh`)
    -- is exactly `b`'s OWN naturality (`b.nat (k , refl)`). `β` is then
    -- DEFINITIONAL: `app (lam b) a = b(x,a)`.
    ----------------------------------------------------------------------

    lam : Tm (⌊ 𝒞 ⌋ ▷⁻ A) B → Tm ⌊ 𝒞 ⌋ Π⁺
    lam b = record { tm = ltm ; nat = λ f → Πfib-≡ (act f (ltm _)) (ltm _) refl }
      where
      ltm : ∀ x → Πfib A B x
      ltm x = mk (λ y h a → Tm.tm b (y , a))
                 (λ y z h k a → Tm.nat b (k , refl))

    app-lam : (b : Tm (⌊ 𝒞 ⌋ ▷⁻ A) B) (x : Ob) (a : A.fam x) →
              app (Tm.tm (lam b) x) a ≡ Tm.tm b (x , a)
    app-lam b x a = refl
