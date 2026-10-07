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

-- entry n: its body's value at the table before it (an ARGUMENT: shared)
extendAt : ℕ → Tbl → RTm ε → Tbl
extendAt n t b = mkT (suc n) (ttele t ▸ᵗ NbE.eval t efuel 0 [] b)

-- the table of a telescope, walked as `lookupK` walks it
goT : ℕ → KTele → Tbl
goT zero    _       = mkT 0 ∅ᵗ
goT (suc n) (T ▸ e) = extendAt n (goT n T) (kBody e)
goT (suc n) ∅       = mkT (suc n) ∅ᵗ

-- ★ the table of a signature — independent of anything but its telescope,
--   so the table of an extension unfolds to `extendAt` of the old one
mkTbl : KSig → Tbl
mkTbl 𝒮 = goT (KSig.len 𝒮) (KSig.tele 𝒮)

------------------------------------------------------------------------
-- Soundness, along the telescope.
------------------------------------------------------------------------

private
  ==-sound : (m n : ℕ) → (m == n) ≡ true → m ≡ n
  ==-sound zero    zero    e = refl
  ==-sound zero    (suc n) ()
  ==-sound (suc m) zero    ()
  ==-sound (suc m) (suc n) e = cong suc (==-sound m n e)

  tlen-goT : (n : ℕ) (T : KTele) → tlen (goT n T) ≡ n
  tlen-goT zero    _       = refl
  tlen-goT (suc n) (T ▸ e) = refl
  tlen-goT (suc n) ∅       = refl

module _ (𝒮 : KSig) where
  open import DirectedHoTT.Spec.Reduction 𝒮 using ( _≅_; crfl; ctrn; cred; δref )
  open TO 𝒮 using ( TblOK; TblReads )
  
  -- the telescope (n , T) is a prefix of 𝒮's: its names are 𝒮's, with 𝒮's bodies
  record KPrefix (n : ℕ) (T : KTele) : Set where
    constructor kprefix
    field
      kinc   : ∀ {d} → d <ˢ n → d <ˢ KSig.size 𝒮
      kagree : ∀ {d} → d <ˢ n → kBody (lookupK n T d) ≡ KSig.body 𝒮 d
  open KPrefix

  private
    ==-refl : (n : ℕ) → (n == n) ≡ true
    ==-refl zero    = refl
    ==-refl (suc n) = ==-refl n

    lookK-here : (n : ℕ) (T : KTele) (e : KEntry) → lookupK (suc n) (T ▸ e) n ≡ e
    lookK-here n T e = subst (λ b → pickK b e (lookupK n T n) ≡ e) (sym (==-refl n)) refl

    -- lookups past the new entry
    lookK-there : (n : ℕ) (T : KTele) (e : KEntry) {d : ℕ} → (d == n) ≡ false →
                  lookupK (suc n) (T ▸ e) d ≡ lookupK n T d
    lookK-there n T e {d} f = subst (λ b → pickK b e (lookupK n T d) ≡ lookupK n T d) (sym f) refl

    lookT-step : (n : ℕ) (t : Tbl) (v : Val) (d : ℕ) → tlen t ≡ n →
                 lookupT (mkT (suc n) (ttele t ▸ᵗ v)) d ≡ pickV (d == n) v (lookupT t d)
    lookT-step n (mkT .n T) v d refl = refl

    pickV-true : {v w : Val} {b : Bool} → b ≡ true → pickV b v w ≡ v
    pickV-true refl = refl

    pickV-false : {v w : Val} {b : Bool} → b ≡ false → pickV b v w ≡ w
    pickV-false refl = refl

    shrinkK : {n : ℕ} {T : KTele} {e : KEntry} → KPrefix (suc n) (T ▸ e) → KPrefix n T
    shrinkK {n} {T} {e} (kprefix i a) =
      kprefix (λ p → i (<-there p))
              (λ {d} p → trans (sym (cong kBody (lookK-there n T e (<ˢ→≠ p)))) (a (<-there p)))
      where
      <ˢ→≠ : ∀ {d m} → d <ˢ m → (d == m) ≡ false
      <ˢ→≠ {d} {m} p = ≠-from p
        where
        ≠-from : ∀ {d m} → d <ˢ m → (d == m) ≡ false
        ≠-from {d} {suc d} <-here = ==-suc d
          where
          ==-suc : (d : ℕ) → (d == suc d) ≡ false
          ==-suc zero    = refl
          ==-suc (suc d) = ==-suc d
        ≠-from {d} {suc m} (<-there q) = lt→≠ d m q
          where
          lt→≠ : (d m : ℕ) → d <ˢ m → (d == suc m) ≡ false
          lt→≠ zero    m       q        = refl
          lt→≠ (suc d) zero    ()
          lt→≠ (suc d) (suc m) <-here   = lt→≠' d
            where
            lt→≠' : (d : ℕ) → (d == suc (suc d)) ≡ false
            lt→≠' zero    = refl
            lt→≠' (suc d) = lt→≠' d
          lt→≠ (suc d) (suc m) (<-there q) = lt→≠ d m (down q)
            where
            down : ∀ {a b} → suc a <ˢ b → a <ˢ b
            down {a} {suc .(suc a)} <-here = <-there <-here
            down {a} {suc b} (<-there r) = <-there (down r)

  okUpTo : (n : ℕ) (T : KTele) → KPrefix n T → TblOK (goT n T)
  okUpTo zero    _       _   = (λ d → tt) , (λ L d → crfl)
  okUpTo (suc n) ∅       _   = (λ d → tt) , (λ L d → crfl)
  okUpTo (suc n) (T ▸ e) pre = sc , rd
    where
    t   = goT n T
    ih  = okUpTo n T (shrinkK pre)
    v   = NbE.eval t efuel 0 [] (kBody e)
    len≡ = tlen-goT n T

    Σfst₀ : TblOK t → TblSc t
    Σfst₀ (c , _) = c

    -- the new entry is 𝒮's entry n
    body≡ : kBody e ≡ KSig.body 𝒮 n
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
  mkTbl-ok = okUpTo (KSig.len 𝒮) (KSig.tele 𝒮) (kprefix (λ p → p) (λ p → refl))
