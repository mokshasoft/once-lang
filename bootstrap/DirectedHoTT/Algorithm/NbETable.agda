-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE SIGNATURE'S VALUE TABLE, and its soundness
--                      (PLAN-REF, E4).
--
-- `mkTbl`: entry m's value is its body evaluated against the table of the
-- entries BEFORE it — the same telescope order as the signature, and the
-- same acyclicity.  The prefix table is passed as an ARGUMENT (`extendAt`),
-- so Agda shares it: every entry is evaluated once, however often it is
-- forced.
--
-- `mkTbl-ok`: the table is sound (`Algorithm/NbE/TblOK`), along the
-- telescope — entry m is closed (evaluation preserves scope, at the prefix
-- table) and reads as `ref m` (δ, then evaluation soundness at the prefix
-- table, which is sound by the induction hypothesis).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbETable where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; _,_; ⊤; tt )
open import Agda.Builtin.Nat using ( zero; suc; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Algorithm.NbE.Value
open import DirectedHoTT.Algorithm.NbERead using ( Sc; TblSc )
import DirectedHoTT.Algorithm.NbE.TblOK as TO
import DirectedHoTT.Algorithm.NbE as NbE
import DirectedHoTT.Algorithm.NbEScope as Scope
import DirectedHoTT.Algorithm.NbESound as Sound

-- the fuel an entry's body is evaluated with
efuel : ℕ
efuel = 100000

-- the next entry: its body's value at the table before it (an ARGUMENT: shared)
extendAt : Tbl → RTm ε → Tbl
extendAt t b = t ▸T NbE.eval t efuel 0 [] b

-- n levels with no entry (the lowest names of a telescope shorter than its length)
gapsᵗ : ℕ → TVals
gapsᵗ zero    = []ᵗ
gapsᵗ (suc n) = skipᵗ (gapsᵗ n)

-- the table of a telescope, entry n at level n as `lookupK` places it
goT : ℕ → DefTele → Tbl
goT zero    _       = ∅T
goT (suc n) (T ▸ e) = extendAt (goT n T) (kBody e)
goT (suc n) ∅       = mkT (gapsᵗ (suc n))

-- ★ the table of a signature — independent of anything but its telescope,
--   so the table of an extension unfolds to `extendAt` of the old one
mkTbl : Defs → Tbl
mkTbl 𝒮 = goT (Defs.len 𝒮) (Defs.tele 𝒮)

------------------------------------------------------------------------
-- Soundness, along the telescope.
------------------------------------------------------------------------

private
  ==-sound : (m n : ℕ) → (m == n) ≡ true → m ≡ n
  ==-sound zero    zero    e = refl
  ==-sound zero    (suc n) ()
  ==-sound (suc m) zero    ()
  ==-sound (suc m) (suc n) e = cong suc (==-sound m n e)

  vlen : TVals → ℕ
  vlen []ᵗ        = zero
  vlen (v ∷ᵗ us)  = suc (vlen us)
  vlen (skipᵗ us) = suc (vlen us)

  vlen-snoc : (us : TVals) (v : Val) → vlen (snocᵗ us v) ≡ suc (vlen us)
  vlen-snoc []ᵗ        v = refl
  vlen-snoc (w ∷ᵗ ws)  v = cong suc (vlen-snoc ws v)
  vlen-snoc (skipᵗ ws) v = cong suc (vlen-snoc ws v)

  vlen-gaps : (n : ℕ) → vlen (gapsᵗ n) ≡ n
  vlen-gaps zero    = refl
  vlen-gaps (suc n) = cong suc (vlen-gaps n)

  -- the table of (n , T) has exactly n levels
  vlen-goT : (n : ℕ) (T : DefTele) → vlen (tvals (goT n T)) ≡ n
  vlen-goT zero    _       = refl
  vlen-goT (suc n) (T ▸ e) = trans (vlen-snoc (tvals (goT n T)) _) (cong suc (vlen-goT n T))
  vlen-goT (suc n) ∅       = vlen-gaps (suc n)

  -- ★ one lookup in an extended list: the new entry at its level, else the old list
  look-snoc : (us : TVals) (v : Val) (k d : ℕ) →
              lookupL (snocᵗ us v) k d ≡ pickV (k == vlen us) v (lookupL us k d)
  look-snoc []ᵗ        v zero    d = refl
  look-snoc []ᵗ        v (suc k) d = refl
  look-snoc (w ∷ᵗ ws)  v zero    d = refl
  look-snoc (w ∷ᵗ ws)  v (suc k) d = look-snoc ws v k d
  look-snoc (skipᵗ ws) v zero    d = refl
  look-snoc (skipᵗ ws) v (suc k) d = look-snoc ws v k d

  -- a gap reads as the stuck reference
  look-gaps : (n k d : ℕ) → lookupL (gapsᵗ n) k d ≡ vref d
  look-gaps zero    k       d = refl
  look-gaps (suc n) zero    d = refl
  look-gaps (suc n) (suc k) d = look-gaps n k d

module _ (𝒮 : Defs) where
  open import DirectedHoTT.Spec.Reduction 𝒮 using ( _≅_; crfl; ctrn; cred; δref )
  open TO 𝒮 using ( TblOK; TblReads )
  
  -- the telescope (n , T) is a prefix of 𝒮's: its names are 𝒮's, with 𝒮's bodies
  record KPrefix (n : ℕ) (T : DefTele) : Set where
    constructor kprefix
    field
      kinc   : ∀ {d} → d <ˢ n → d <ˢ Defs.size 𝒮
      kagree : ∀ {d} → d <ˢ n → kBody (lookupK n T d) ≡ Defs.body 𝒮 d
  open KPrefix

  private
    ==-refl : (n : ℕ) → (n == n) ≡ true
    ==-refl zero    = refl
    ==-refl (suc n) = ==-refl n

    lookK-here : (n : ℕ) (T : DefTele) (e : Def) → lookupK (suc n) (T ▸ e) n ≡ e
    lookK-here n T e = subst (λ b → pickK b e (lookupK n T n) ≡ e) (sym (==-refl n)) refl

    lookT-step : (n : ℕ) (t : Tbl) (v : Val) (d : ℕ) → vlen (tvals t) ≡ n →
                 lookupT (t ▸T v) d ≡ pickV (d == n) v (lookupT t d)
    lookT-step .(vlen us) (mkT us) v d refl = look-snoc us v d d

    pickV-true : {v w : Val} {b : Bool} → b ≡ true → pickV b v w ≡ v
    pickV-true refl = refl

    pickV-false : {v w : Val} {b : Bool} → b ≡ false → pickV b v w ≡ w
    pickV-false refl = refl

    shrinkK : {n : ℕ} {T : DefTele} {e : Def} → KPrefix (suc n) (T ▸ e) → KPrefix n T
    shrinkK {n} {T} {e} (kprefix i a) =
      kprefix (λ p → i (<-there p))
              (λ {d} p → trans (sym (cong kBody (lookupK-▸ p))) (a (<-there p)))

  okUpTo : (n : ℕ) (T : DefTele) → KPrefix n T → TblOK (goT n T)
  okUpTo zero    _       _   = (λ d → tt) , (λ L d → crfl)
  okUpTo (suc n) ∅       _   =
    (λ d → subst (Sc 0) (sym (look-gaps (suc n) d d)) tt) ,
    (λ L d → subst (λ w → ref d ≅ ⌊ w ⌋ L) (sym (look-gaps (suc n) d d)) crfl)
  okUpTo (suc n) (T ▸ e) pre = sc , rd
    where
    t   = goT n T
    ih  = okUpTo n T (shrinkK pre)
    v   = NbE.eval t efuel 0 [] (kBody e)
    len≡ = vlen-goT n T

    Σfst₀ : TblOK t → TblSc t
    Σfst₀ (c , _) = c

    -- the new entry is 𝒮's entry n
    body≡ : kBody e ≡ Defs.body 𝒮 n
    body≡ = trans (sym (cong kBody (lookK-here n T e))) (kagree pre <-here)


    sc : TblSc (goT (suc n) (T ▸ e))
    sc d = scAt d (d == n) refl
      where
      scAt : (d : ℕ) (b : Bool) → (d == n) ≡ b → Sc 0 (lookupT (goT (suc n) (T ▸ e)) d)
      scAt d true  eq = subst (Sc 0) (sym (trans (lookT-step n t v d len≡) (pickV-true eq)))
                              (Scope.sc-eval t (Σfst₀ ih) efuel 0 [] (kBody e) tt)
      scAt d false eq = subst (Sc 0) (sym (trans (lookT-step n t v d len≡) (pickV-false eq))) (Σfst₀ ih d)

    rd : TblReads (goT (suc n) (T ▸ e))
    rd L d = rdAt d (d == n) refl
      where
      Σsnd : TblOK t → TblReads t
      Σsnd (_ , r) = r
      -- the new entry: δ, then the body's value at the prefix table
      entry : ref n ≅ ⌊ v ⌋ L
      entry = ctrn (cred (δref n (kinc pre <-here)))
                (subst (λ b → εwkTm b ≅ ⌊ v ⌋ L) body≡
                  (ctrn (Sound.≡→≅ 𝒮 t ih (subTm-cong (λ ()) (kBody e)))
                        (Sound.S-eval 𝒮 t ih efuel 0 [] (kBody e) L tt)))
      rdAt : (d : ℕ) (b : Bool) → (d == n) ≡ b → ref d ≅ ⌊ lookupT (goT (suc n) (T ▸ e)) d ⌋ L
      rdAt d true eq with ==-sound d n eq
      ... | refl = subst (λ w → ref d ≅ ⌊ w ⌋ L) (sym (trans (lookT-step n t v d len≡) (pickV-true eq))) entry
      rdAt d false eq =
        subst (λ w → ref d ≅ ⌊ w ⌋ L) (sym (trans (lookT-step n t v d len≡) (pickV-false eq))) (Σsnd ih L d)

  mkTbl-ok : TblOK (mkTbl 𝒮)
  mkTbl-ok = okUpTo (Defs.len 𝒮) (Defs.tele 𝒮) (kprefix (λ p → p) (λ p → refl))
