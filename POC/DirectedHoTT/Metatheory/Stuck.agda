------------------------------------------------------------------------
-- STUCKNESS, keyed.  `stk k t`: t can never reduce so that an eliminator
-- of key k fires on it.
--
-- The metatheory had sixteen hand-written stuckness predicates (`spine?`,
-- `natstk?`, `mustk?`, …), one per eliminator family, each with its own
-- preservation, renaming and neutral lemmas.  They are ONE analysis:
--
--   * an ELIMINATOR answers by its principal argument at ITS OWN key —
--     the same answer under every key (a redex's root is an eliminator,
--     so the key never matters at a redex);
--   * an INTRODUCTION is stuck unless the key's eliminator consumes it
--     (`natK` at `nzero`/`nsuc`, `muK` at `con`, …);
--   * three formers look into a field under a few keys: `⌜Hom⌝`'s code,
--     `hrefl`'s code, and `ap` (inert under `nopwK`).
--
-- The old names are abbreviations (`natstk? = stk natK`), so every
-- definitional equation the consumers rely on still holds.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Stuck where

open import DirectedHoTT.Spec.Scope using ( Cx; _∙; vz; vs )
open import DirectedHoTT.Spec.Syntax
  using ( module KS; KCon; tm; RTm; var; lam; app; absurd; ordtr; fst; snd; ⌜Hom⌝; hrefl; tr; ap
        ; jsub; nzero; nsuc; natrec; ielim; dpay; dih; fcase; fcase0; psplit; ref
        ; `lam; `⌜base⌝; `⌜Π⌝; `⌜Σ⌝; `⌜Id⌝; `idrefl; `nzero; `nsuc; `con
        ; `dι; `dσ; `dρ; `fzero; `fsuc; `⌜Nat⌝; `⌜IMu⌝; `⌜Fin⌝; `⌜Unit⌝ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )

private
  variable
    Γ : Cx

-- the eliminator families, one key each (`stableAK` is `stablecdK` that
-- also refuses `⌜Nat⌝`; `pathK`/`apK`/`nopwK`/`deadK` are the W2 path keys)
data Key : Set where
  spineK stablecdK stableAK pathK nopwK deadK apK idK natK natcK muK finK dK : Key

var? : RTm Γ → 𝔹
var? (var _) = true
var? _       = false

pick : 𝔹 → 𝔹 → 𝔹 → 𝔹
pick true  x y = x
pick false x y = y

-- ★ the whole key-dependence on introductions: does key k's eliminator
--   NOT consume former c?  (`true` = c is stuck for k)
-- the stable codes: everything but the codes `El` decodes to a former
introcd : KCon tm → 𝔹
introcd `⌜Π⌝    = false
introcd `⌜Σ⌝    = false
introcd `⌜base⌝ = false
introcd `⌜Id⌝   = false
introcd `⌜Unit⌝ = false
introcd `⌜IMu⌝  = false
introcd `⌜Fin⌝  = false
introcd _       = true

intro : Key → KCon tm → 𝔹
intro spineK    `⌜Π⌝    = true
intro spineK    `⌜Id⌝   = true
intro spineK    `idrefl = true
intro spineK    _       = false
intro stablecdK c       = introcd c
intro stableAK  `⌜Nat⌝  = false
intro stableAK  c       = introcd c
intro pathK     `lam    = false
intro nopwK     `⌜Π⌝    = false
intro deadK     `⌜Π⌝    = false
intro idK       `idrefl = false
intro natK      `nzero  = false
intro natK      `nsuc   = false
intro natcK     `⌜Nat⌝  = false
intro muK       `con    = false
intro finK      `fzero  = false
intro finK      `fsuc   = false
intro dK        `dι     = false
intro dK        `dσ     = false
intro dK        `dρ     = false
intro _         _       = true

stk     : Key → RTm Γ → 𝔹
ordstk? : RTm Γ → RTm Γ → RTm Γ → 𝔹
ordS?   : 𝔹 → RTm Γ → 𝔹
trstk?  : RTm (Γ ∙) → RTm Γ → 𝔹
trlam?  : RTm (Γ ∙) → 𝔹
hstk?   : RTm Γ → RTm Γ → 𝔹
homv    : Key → RTm Γ → 𝔹                -- ⌜Hom⌝ c _ _, by its code
hreflv  : Key → RTm Γ → RTm Γ → 𝔹        -- hrefl c t
apv     : Key → RTm Γ → 𝔹                -- ap _ _ p, by its path

-- eliminators: the principal argument at the eliminator's own key
stk k (var _)            = true
stk k (app t _)          = stk spineK t
stk k (fst t)            = stk spineK t
stk k (snd t)            = stk spineK t
stk k (absurd _ _)       = true
stk k (ordtr a t u _ _)  = ordstk? a t u
stk k (tr d p _)         = trstk? d p
stk k (jsub _ p _)       = stk idK p
stk k (natrec _ _ n)     = stk natK n
stk k (ielim _ _ _ t)    = stk muK t
stk k (dpay _ _ C)       = stk dK C
stk k (dih _ _ C _)      = stk dK C
stk k (fcase t _ _)      = stk finK t
stk k (fcase0 _)         = true
stk k (psplit _ q)       = stk spineK q
stk k (ref _)            = false
-- the three formers that look into a field
stk k (ap _ _ p)         = apv k p
stk k (⌜Hom⌝ c _ _)      = homv k c
stk k (hrefl c t)        = hreflv k c t
-- introductions
stk k (KS.node c _)      = intro k c

apv nopwK p = true
apv k     p = stk apK p

homv stablecdK c = stk stableAK c
homv stableAK  c = stk stableAK c
homv nopwK     c = stk nopwK c
homv deadK     c = stk deadK c
homv _         c = true

hreflv spineK c t = hstk? c t
hreflv pathK  c t = stk stablecdK c
hreflv apK    c t = stk stablecdK c
hreflv deadK  c t = stk deadK c
hreflv _      c t = true

ordstk? nzero t u    = false
ordstk? (nsuc a) t u = ordS? (stk natK t) u
ordstk? a t u        = stk natK a

ordS? true  u = true
ordS? false u = stk natK u

trstk? d (lam f)     = trlam? d
trstk? d (hrefl c s) = pick (var? d) (stk nopwK c) (stk stablecdK c)
trstk? d p           = stk pathK p

trlam? (⌜Hom⌝ c a (var vz))     = stk deadK c
trlam? (⌜Hom⌝ c a (var (vs x))) = true
trlam? _                        = false

hstk? c t = pick (stk nopwK c) (pick (stk natK t) true (stk natcK c)) false
