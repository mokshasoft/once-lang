------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 9 — DEPENDENT DIRECTED J = the REPRESENTABLE Π
--
-- The crown jewel, case (a): the dependent function type over a REPRESENTABLE
-- domain `Hom(a,-)`. Its fibre is an END, `∫_{(x,f)} B(x,f)` — but for the
-- representable it COLLAPSES by (directed) Yoneda to `B(a , id)`. So the
-- representable Π IS fully-dependent directed path induction:
--
--     given a motive `B` over the coslice `⌊C⌋ ▷ Yo⁺ C a` (objects `(x , f)`
--     with `f : a ⇒ x` — a path out of `a`) and a base point `d : B(a , id)`,
--     there is a canonical SECTION `Jᵈ d`, natural, with `Jᵈ d (a,id) ≡ d`.
--
-- The eliminator is `B.act (f , unitˡ f) d` — transport along the unique
-- coslice morphism `(a,id) ⇒ (x,f)`. `DirCwFJ`'s `Jᶜ` did this for a motive
-- depending only on the endpoint `x`; here the motive depends on the PATH `f`
-- too (`B` over the whole coslice), the fully general based `J`. Naturality
-- and β reuse the `Σ⁺` transport toolkit (`Σ≡` + `uip`) — the representable
-- end needs no extra coherence beyond what the Grothendieck already supplies.
-- (General `A` — the non-representable Π — is the wedge-carrying record; this
-- is the case the pattern pre-solves.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirPi where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; Σ; _,_ )
open Σ
open import poc.OCP0009.NbEPDirCwF using ( Ctx; Cat; ⌊_⌋; Ty⁺; Tm; _▷_ )
open import poc.OCP0009.NbEPDirCwFJ using ( Yo⁺ )
open import poc.OCP0009.NbEPDirSig using ( uip; Σ≡ )

module _ (C : Cat) (a : Cat.Ob C) (B : Ty⁺ (⌊ C ⌋ ▷ Yo⁺ C a)) where
  private
    module C = Cat C
    module B = Ty⁺ B
  open C using ( Ob; _⇒_; idₒ; _⨾_; unitˡ )
  open Ctx (⌊ C ⌋ ▷ Yo⁺ C a) using () renaming ( _⨾_ to _⨾▷_ )

  -- The canonical coslice morphism `(a , id) ⇒ (x , f)` (there is exactly one
  -- for each `f`, its first component `f` itself — this is representability).
  ! : ∀ {x} (f : a ⇒ x) → Ctx._⇒_ (⌊ C ⌋ ▷ Yo⁺ C a) (a , idₒ) (x , f)
  ! f = f , unitˡ f

  -- Dependent directed J: the section built from the base point.
  Jᵈ : B.fam (a , idₒ) → Tm (⌊ C ⌋ ▷ Yo⁺ C a) B
  Jᵈ d = record
    { tm  = λ p → B.act (! (snd p)) d
    ; nat = λ {p} {q} m →
        trans (sym (B.act⨾ (! (snd p)) m d))
              (cong (λ n → B.act n d)
                    (Σ≡ (snd m) (uip _ _))) }

  -- β / computation: at the reflexive path `(a , id)`, `Jᵈ d` returns `d`.
  Jᵈ-β : (d : B.fam (a , idₒ)) → Tm.tm (Jᵈ d) (a , idₒ) ≡ d
  Jᵈ-β d = trans (cong (λ n → B.act n d) (Σ≡ refl (uip _ _))) (B.actid d)

  -- η / uniqueness: every section is `Jᵈ` of its value at `(a , id)`. The
  -- proof is the section's OWN naturality — the representable end is rigid.
  -- Together with `Jᵈ-β` this is the DEPENDENT Yoneda iso: sections of `B`
  -- over the coslice `≅ B(a , id)`, pointwise.
  Jᵈ-η : (s : Tm (⌊ C ⌋ ▷ Yo⁺ C a) B) (p : Ctx.Ob (⌊ C ⌋ ▷ Yo⁺ C a)) →
         Tm.tm (Jᵈ (Tm.tm s (a , idₒ))) p ≡ Tm.tm s p
  Jᵈ-η s p = Tm.nat s (! (snd p))
