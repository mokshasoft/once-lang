------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.Typed.Func
--
-- A metalevel universe of strictly-positive functor codes (Func) and
-- a matching Tarski universe of closed types (TyClosed).
--
-- WHY THIS EXISTS:
--   StrongCCL CCT3's Ty has μ : (Ty → Ty) → Ty taking an arbitrary
--   metalevel function. There is no decision procedure for "what
--   syntactic functor produced this μ", so encode-ty cannot be
--   total over Ty without losing information.
--
--   The honest fix is to recognise that a verified Once compiler does
--   not see arbitrary metalevel functors anyway — every user-defined
--   datatype comes with an explicit syntactic shape. We capture that
--   shape as a Func code and define a Tarski universe TyClosed of
--   types built only from coded μ-functors. Then:
--
--     - lift : TyClosed → Ty           (forgetful: gives the real type)
--     - ⟦_⟧  : Func → (Ty → Ty)        (functor decoder)
--     - encode-tyc (in .TyEncodingCoded) is faithful on TyClosed.
--
-- DESIGN:
--
--   data TyClosed where         data Func where
--     Unit, Void                  K   : TyClosed → Func   -- constant
--     _×_, _⊎_, _⇒_               Id  : Func              -- identity
--     Mu  : Func → TyClosed       _⊕_ : Func → Func → Func
--                                 _⊗_ : Func → Func → Func
--
--   The two are mutually recursive: TyClosed.Mu carries a Func, and
--   Func.K carries a TyClosed (so closed types can appear as constants
--   inside functors, e.g., `K (Mu (K Unit ⊕ Id))` for `λ X. List Unit`).
--
-- PHASE-2 SCOPE:
--   For Phase 2 the Func grammar covers:
--     - Constants (K), identity (Id), sum (⊕), product (⊗)
--   Closure under exponential (Arr, fixed exponent on the left), nested
--   recursion (Mu_F), and explicit Sigma may be added in Phase 3 if
--   downstream uses need them. The current grammar already covers all
--   the SPFs used by Once's standard datatypes (List, Maybe, Tree,
--   Stream, Nat, etc.).
--
-- TOWER LEVEL: CCT3.
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.Typed.Func where

import Theory.Syntax.StrongCCL.CCT3 as Syn

------------------------------------------------------------------------
-- The closed-type universe and the SPF code universe.
--
-- Mutually recursive: a closed type's μ stores a Func; a Func's K
-- stores a closed type.
------------------------------------------------------------------------

mutual

  data TyClosed : Set where
    Unit  : TyClosed
    Void  : TyClosed
    _×_   : TyClosed → TyClosed → TyClosed
    _⊎_   : TyClosed → TyClosed → TyClosed
    _⇒_   : TyClosed → TyClosed → TyClosed
    Mu    : Func → TyClosed

  data Func : Set where
    K     : TyClosed → Func
    Id    : Func
    _⊕_   : Func → Func → Func
    _⊗_   : Func → Func → Func

infixr 7 _×_ _⊗_
infixr 6 _⇒_
infixr 5 _⊎_ _⊕_

------------------------------------------------------------------------
-- Forgetful map TyClosed → Ty and functor decoder Func → (Ty → Ty).
--
-- Mutually recursive following the data definition.
------------------------------------------------------------------------

mutual

  lift : TyClosed → Syn.Ty
  lift Unit    = Syn.Unit
  lift Void    = Syn.Void
  lift (a × b) = lift a Syn.× lift b
  lift (a ⊎ b) = lift a Syn.⊎ lift b
  lift (a ⇒ b) = lift a Syn.⇒ lift b
  lift (Mu φ)  = Syn.μ ⟦ φ ⟧

  ⟦_⟧ : Func → (Syn.Ty → Syn.Ty)
  ⟦ K T   ⟧ _ = lift T
  ⟦ Id    ⟧ X = X
  ⟦ φ ⊕ ψ ⟧ X = ⟦ φ ⟧ X Syn.⊎ ⟦ ψ ⟧ X
  ⟦ φ ⊗ ψ ⟧ X = ⟦ φ ⟧ X Syn.× ⟦ ψ ⟧ X
