------------------------------------------------------------------------
-- Normalize.NoRedexRebuild: NoRedex proofs for rebuild helpers
--
-- This module contains NoRedex proofs for:
-- - inr chain compositions
-- - rebuild-N functions
-- - ret-no-N and ret-yes functions
------------------------------------------------------------------------

module normalizer.Implementation.Normalize.NoRedexRebuild where

open import normalizer.Implementation.Normalize.Rebuild public

------------------------------------------------------------------------
-- Helper: inr chain compositions are NoRedex
------------------------------------------------------------------------

-- Chains ending with inl (for positions 0-12)
nr-inr-chain-1 : ∀ {A B C} → NoRedex (inr {C} ∘ inl {A} {B})
nr-inr-chain-1 = nr-comp nr-inr nr-inl nis-inr nis-inl

nr-inr-chain-2 : ∀ {A B C D} → NoRedex (inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-2 = nr-comp nr-inr nr-inr-chain-1 nis-inr nis-comp

nr-inr-chain-3 : ∀ {A B C D E} → NoRedex (inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-3 = nr-comp nr-inr nr-inr-chain-2 nis-inr nis-comp

nr-inr-chain-4 : ∀ {A B C D E F} → NoRedex (inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-4 = nr-comp nr-inr nr-inr-chain-3 nis-inr nis-comp

nr-inr-chain-5 : ∀ {A B C D E F G} → NoRedex (inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-5 = nr-comp nr-inr nr-inr-chain-4 nis-inr nis-comp

nr-inr-chain-6 : ∀ {A B C D E F G H} → NoRedex (inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-6 = nr-comp nr-inr nr-inr-chain-5 nis-inr nis-comp

nr-inr-chain-7 : ∀ {A B C D E F G H I} → NoRedex (inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-7 = nr-comp nr-inr nr-inr-chain-6 nis-inr nis-comp

nr-inr-chain-8 : ∀ {A B C D E F G H I J} → NoRedex (inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-8 = nr-comp nr-inr nr-inr-chain-7 nis-inr nis-comp

nr-inr-chain-9 : ∀ {A B C D E F G H I J K} → NoRedex (inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-9 = nr-comp nr-inr nr-inr-chain-8 nis-inr nis-comp

nr-inr-chain-10 : ∀ {A B C D E F G H I J K L} → NoRedex (inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-10 = nr-comp nr-inr nr-inr-chain-9 nis-inr nis-comp

nr-inr-chain-11 : ∀ {A B C D E F G H I J K L M} → NoRedex (inr {M} ∘ inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-11 = nr-comp nr-inr nr-inr-chain-10 nis-inr nis-comp

nr-inr-chain-12 : ∀ {A B C D E F G H I J K L M N} → NoRedex (inr {N} ∘ inr {M} ∘ inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-12 = nr-comp nr-inr nr-inr-chain-11 nis-inr nis-comp

nr-inr-chain-13 : ∀ {A B C D E F G H I J K L M N O} → NoRedex (inr {O} ∘ inr {N} ∘ inr {M} ∘ inr {L} ∘ inr {K} ∘ inr {J} ∘ inr {I} ∘ inr {H} ∘ inr {G} ∘ inr {F} ∘ inr {E} ∘ inr {D} ∘ inr {C} ∘ inl {A} {B})
nr-inr-chain-13 = nr-comp nr-inr nr-inr-chain-12 nis-inr nis-comp

-- Rightmost chain (no inl at end) for position 14
nr-inr-end-1 : ∀ {A B} → NoRedex (inr {A} {B})
nr-inr-end-1 = nr-inr

nr-inr-end-2 : ∀ {A B C} → NoRedex (inr {A} ∘ inr {B} {C})
nr-inr-end-2 = nr-comp nr-inr nr-inr-end-1 nis-inr nis-inr

nr-inr-end-3 : ∀ {A B C D} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} {D})
nr-inr-end-3 = nr-comp nr-inr nr-inr-end-2 nis-inr nis-comp

nr-inr-end-4 : ∀ {A B C D E} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} {E})
nr-inr-end-4 = nr-comp nr-inr nr-inr-end-3 nis-inr nis-comp

nr-inr-end-5 : ∀ {A B C D E F} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} {F})
nr-inr-end-5 = nr-comp nr-inr nr-inr-end-4 nis-inr nis-comp

nr-inr-end-6 : ∀ {A B C D E F G} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} {G})
nr-inr-end-6 = nr-comp nr-inr nr-inr-end-5 nis-inr nis-comp

nr-inr-end-7 : ∀ {A B C D E F G H} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} {H})
nr-inr-end-7 = nr-comp nr-inr nr-inr-end-6 nis-inr nis-comp

nr-inr-end-8 : ∀ {A B C D E F G H I} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} {I})
nr-inr-end-8 = nr-comp nr-inr nr-inr-end-7 nis-inr nis-comp

nr-inr-end-9 : ∀ {A B C D E F G H I J} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} {J})
nr-inr-end-9 = nr-comp nr-inr nr-inr-end-8 nis-inr nis-comp

nr-inr-end-10 : ∀ {A B C D E F G H I J K} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} {K})
nr-inr-end-10 = nr-comp nr-inr nr-inr-end-9 nis-inr nis-comp

nr-inr-end-11 : ∀ {A B C D E F G H I J K L} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} {L})
nr-inr-end-11 = nr-comp nr-inr nr-inr-end-10 nis-inr nis-comp

nr-inr-end-12 : ∀ {A B C D E F G H I J K L M} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} ∘ inr {L} {M})
nr-inr-end-12 = nr-comp nr-inr nr-inr-end-11 nis-inr nis-comp

nr-inr-end-13 : ∀ {A B C D E F G H I J K L M N} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} ∘ inr {L} ∘ inr {M} {N})
nr-inr-end-13 = nr-comp nr-inr nr-inr-end-12 nis-inr nis-comp

nr-inr-end-14 : ∀ {A B C D E F G H I J K L M N O} → NoRedex (inr {A} ∘ inr {B} ∘ inr {C} ∘ inr {D} ∘ inr {E} ∘ inr {F} ∘ inr {G} ∘ inr {H} ∘ inr {I} ∘ inr {J} ∘ inr {K} ∘ inr {L} ∘ inr {M} ∘ inr {N} {O})
nr-inr-end-14 = nr-comp nr-inr nr-inr-end-13 nis-inr nis-comp

------------------------------------------------------------------------
-- NoRedex proofs for rebuild functions
------------------------------------------------------------------------

nr-rebuild-0 : NoRedex rebuild-0
nr-rebuild-0 = nr-comp nr-In nr-inl nis-In nis-inl

nr-rebuild-1 : NoRedex rebuild-1
nr-rebuild-1 = nr-comp nr-In nr-inr-chain-1 nis-In nis-comp

nr-rebuild-2 : NoRedex rebuild-2
nr-rebuild-2 = nr-comp nr-In nr-inr-chain-2 nis-In nis-comp

nr-rebuild-3 : NoRedex rebuild-3
nr-rebuild-3 = nr-comp nr-In nr-inr-chain-3 nis-In nis-comp

nr-rebuild-4 : NoRedex rebuild-4
nr-rebuild-4 = nr-comp nr-In nr-inr-chain-4 nis-In nis-comp

nr-rebuild-5 : NoRedex rebuild-5
nr-rebuild-5 = nr-comp nr-In nr-inr-chain-5 nis-In nis-comp

nr-rebuild-6 : NoRedex rebuild-6
nr-rebuild-6 = nr-comp nr-In nr-inr-chain-6 nis-In nis-comp

nr-rebuild-7 : NoRedex rebuild-7
nr-rebuild-7 = nr-comp nr-In nr-inr-chain-7 nis-In nis-comp

nr-rebuild-8 : NoRedex rebuild-8
nr-rebuild-8 = nr-comp nr-In nr-inr-chain-8 nis-In nis-comp

nr-rebuild-9 : NoRedex rebuild-9
nr-rebuild-9 = nr-comp nr-In nr-inr-chain-9 nis-In nis-comp

nr-rebuild-10 : NoRedex rebuild-10
nr-rebuild-10 = nr-comp nr-In nr-inr-chain-10 nis-In nis-comp

nr-rebuild-11 : NoRedex rebuild-11
nr-rebuild-11 = nr-comp nr-In nr-inr-chain-11 nis-In nis-comp

nr-rebuild-12 : NoRedex rebuild-12
nr-rebuild-12 = nr-comp nr-In nr-inr-chain-12 nis-In nis-comp

nr-rebuild-13 : NoRedex rebuild-13
nr-rebuild-13 = nr-comp nr-In nr-inr-chain-13 nis-In nis-comp

nr-rebuild-14 : NoRedex rebuild-14
nr-rebuild-14 = nr-comp nr-In nr-inr-end-14 nis-In nis-comp

------------------------------------------------------------------------
-- NoRedex proofs for ret-yes and ret-no functions
------------------------------------------------------------------------

nr-ret-yes : ∀ {A} → NoRedex (ret-yes {A})
nr-ret-yes = nr-comp nr-inl nr-terminal nis-inl nis-terminal

nr-ret-no-0 : NoRedex ret-no-0
nr-ret-no-0 = nr-comp nr-inr nr-rebuild-0 nis-inr nis-comp

nr-ret-no-1 : NoRedex ret-no-1
nr-ret-no-1 = nr-comp nr-inr nr-rebuild-1 nis-inr nis-comp

nr-ret-no-2 : NoRedex ret-no-2
nr-ret-no-2 = nr-comp nr-inr nr-rebuild-2 nis-inr nis-comp

nr-ret-no-3 : NoRedex ret-no-3
nr-ret-no-3 = nr-comp nr-inr nr-rebuild-3 nis-inr nis-comp

nr-ret-no-4 : NoRedex ret-no-4
nr-ret-no-4 = nr-comp nr-inr nr-rebuild-4 nis-inr nis-comp

nr-ret-no-5 : NoRedex ret-no-5
nr-ret-no-5 = nr-comp nr-inr nr-rebuild-5 nis-inr nis-comp

nr-ret-no-6 : NoRedex ret-no-6
nr-ret-no-6 = nr-comp nr-inr nr-rebuild-6 nis-inr nis-comp

nr-ret-no-7 : NoRedex ret-no-7
nr-ret-no-7 = nr-comp nr-inr nr-rebuild-7 nis-inr nis-comp

nr-ret-no-8 : NoRedex ret-no-8
nr-ret-no-8 = nr-comp nr-inr nr-rebuild-8 nis-inr nis-comp

nr-ret-no-9 : NoRedex ret-no-9
nr-ret-no-9 = nr-comp nr-inr nr-rebuild-9 nis-inr nis-comp

nr-ret-no-10 : NoRedex ret-no-10
nr-ret-no-10 = nr-comp nr-inr nr-rebuild-10 nis-inr nis-comp

nr-ret-no-11 : NoRedex ret-no-11
nr-ret-no-11 = nr-comp nr-inr nr-rebuild-11 nis-inr nis-comp

nr-ret-no-12 : NoRedex ret-no-12
nr-ret-no-12 = nr-comp nr-inr nr-rebuild-12 nis-inr nis-comp

nr-ret-no-13 : NoRedex ret-no-13
nr-ret-no-13 = nr-comp nr-inr nr-rebuild-13 nis-inr nis-comp

nr-ret-no-14 : NoRedex ret-no-14
nr-ret-no-14 = nr-comp nr-inr nr-rebuild-14 nis-inr nis-comp
