------------------------------------------------------------------------
-- OCP-0009 · W1d — JOACHIMSKI–MATTHES INDUCTIVE SN, and the head-expansion
--                  wall, GONE.
--
-- `SpikeSNX` §5 left one lemma between here and `fund`: SN closed under head
-- expansion when the redex sits UNDER an application.  The spine route was
-- refuted there — not as too bulky, but as unstateable: `_·_` is a function, so
-- `app (lam s) u · sp` with `sp` a variable is a STUCK term, and Agda can
-- neither take nor refute the `β` case against it (`SplitError.UnificationStuck`).
-- The recommendation was to make head-redex-hood a DATATYPE instead.  This
-- module does that, and the wall is gone.
--
-- ★ THE MOVE, in one line.  `_⟶ₕ_` becomes an inductive family `SNRed` with a
--   CONGRUENCE CONSTRUCTOR `snr-app : SNRed t t' → SNRed (app t u) (app t' u)`,
--   and head expansion becomes a CONSTRUCTOR of `SN` rather than a lemma about
--   it.  Then the `Π` case of the logical relation's expansion, which needed the
--   whole spine generalization, is one application of `snr-app` and a
--   structurally smaller recursive call:
--
--       exp (⊩Π _ ⊩F ⊩G) r h =
--         (sn-exp r (projl h) , λ v rv → exp (⊩G v rv) (snr-app r) (projr h v rv))
--
--   No spine, no inversion, nothing stuck.  `SpikeSNX.sn-exp` — the classic
--   `abs` lemma that took a lexicographic induction — is subsumed by the `snr-β`
--   constructor.
--
-- ★ AND THE `SN → Acc` DIRECTION IS NOT NEEDED.  The usual objection to the JM
--   presentation is that its cost moves to proving it sound for accessibility-SN,
--   which is the hard direction.  That obligation does not arise here, because of
--   what the consumer actually wants: `NbEPDirDBDec.dec-conv` takes `t ⟶* n` and
--   `IsNormal n` — WEAK normalization.  And WN falls straight out of the
--   inductive presentation by structural recursion (`wn`/`wne` below), since
--   `sn-exp` records a reduction and the other constructors record congruences.
--   So the theorem delivered to `dec-conv` is WN, which is all it consumes.
--
--   ⚠ Stated honestly: this makes the headline WEAK normalization, not strong.
--   Nothing here proves inductive-`SN` equivalent to accessibility-`SN`; that
--   remains open and is only worth doing if SN itself is wanted as a result.
--   `SpikeSNW`/`SpikeSNX` are unaffected — they are about accessibility-SN and
--   stand as they are.
--
-- DELIVERED, `--safe`, zero postulates, zero holes:
--   `SNe`/`SN`/`SNRed`   the JM presentation over the kernel's real `RTm`
--   ★ `exp`              LR head expansion — the wall, gone
--   ★ `sem-lam`          `fund`'s λ-case, complete
--   `CR1`/`CR2`/`CR3`    now much shorter: `sne-app` is a CONSTRUCTOR, so the
--                        `sn-app-ne` lemma disappears entirely
--   ★ `wn`/`wne`         weak normalization — exactly `dec-conv`'s input
--
-- SCOPE: the logical relation is re-declared here over the inductive `SN`
-- (`SpikeSNW`'s is over accessibility-`SN`).  `SpikeSNW`'s `irrel`/`fwd*`/
-- `bwd*`/`conv-⊩` port VERBATIM — inspect them and none touches `SN` or even
-- membership: the nine non-`Π` cases of `irrel` are `λ _ h → h`, and the
-- transfer lemmas only manipulate the stored whnf reductions.  Not copied here
-- to keep the delta reviewable.  `Σ'` still out of `⊩`, as in `SpikeSNW`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeSNJ where

open import normalizer.Syntax.Types
  using ( _≡_; refl; ¬_; ⊥; ⊥-elim; Σ; _,_; _×_ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; Sub; subTy; subTm; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; _⟶*_; done; step )
open import poc.OCP0009.NbEPDirDBConf
  using ( ⟶*-trans; ⟶*-lam; ⟶*-appˡ; ⟶*-appʳ
        ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-⌜Π⌝ˡ; ⟶*-⌜Π⌝ʳ; ⟶*-⌜Σ⌝ˡ; ⟶*-⌜Σ⌝ʳ )
open import poc.OCP0009.NbEPDirDBInj using ( _⟶ᵀ*_; doneᵀ; stepᵀ )
open import poc.OCP0009.SpikeSNW using ( projl; projr )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- ★ 1. THE JOACHIMSKI–MATTHES PRESENTATION.
--
-- Three mutually inductive families over the kernel's real `RTm`:
--
--   `SNe t`      — `t` is a strongly normalizing NEUTRAL (variable-headed);
--   `SN t`       — `t` is strongly normalizing;
--   `SNRed t t'` — `t` HEAD-reduces to `t'`.
--
-- The two constructors that do all the work:
--   * `sn-exp : SNRed t t' → SN t' → SN t`  — head expansion is a CONSTRUCTOR,
--     so it is never a lemma to prove;
--   * `snr-app : SNRed t t' → SNRed (app t u) (app t' u)` — head reduction is
--     closed under application STRUCTURALLY, which is exactly what the spine
--     route was trying (and failing) to express with a stuck `_·_`.
--
-- Note the `SN` premises on `snr-β`/`snr-βfst`/`snr-βsnd`: they carry the
-- DISCARDED material.  Without them the presentation would be unsound — `β` can
-- throw its argument away, and `(λx. y) Ω ⟶ y` must not make `(λx. y) Ω` normal.
------------------------------------------------------------------------

data SNe {Γ} : RTm Γ → Set
data SN  {Γ} : RTm Γ → Set
data SNRed {Γ} : RTm Γ → RTm Γ → Set

data SNe {Γ} where
  sne-var : (x : Var Γ) → SNe (var x)
  sne-app : {t u : RTm Γ} → SNe t → SN u → SNe (app t u)
  sne-fst : {p : RTm Γ} → SNe p → SNe (fst p)
  sne-snd : {p : RTm Γ} → SNe p → SNe (snd p)

data SN {Γ} where
  sn-ne   : {t : RTm Γ} → SNe t → SN t
  sn-lam  : {t : RTm (Γ ∙)} → SN t → SN (lam t)
  sn-pair : {a b : RTm Γ} → SN a → SN b → SN (pair a b)
  sn-cb   : SN (⌜base⌝ {Γ})
  sn-cΠ   : {c : RTm Γ} {d : RTm (Γ ∙)} → SN c → SN d → SN (⌜Π⌝ c d)
  sn-cΣ   : {c : RTm Γ} {d : RTm (Γ ∙)} → SN c → SN d → SN (⌜Σ⌝ c d)
  -- ★ head expansion, as a CONSTRUCTOR
  sn-exp  : {t t' : RTm Γ} → SNRed t t' → SN t' → SN t

data SNRed {Γ} where
  snr-β    : {s : RTm (Γ ∙)} {u : RTm Γ} → SN u →
             SNRed (app (lam s) u) (subTm (single u) s)
  snr-βfst : {a b : RTm Γ} → SN b → SNRed (fst (pair a b)) a
  snr-βsnd : {a b : RTm Γ} → SN a → SNRed (snd (pair a b)) b
  -- ★ the congruence that replaces the spine
  snr-app  : {t t' u : RTm Γ} → SNRed t t' → SNRed (app t u) (app t' u)
  snr-fst  : {p p' : RTm Γ} → SNRed p p' → SNRed (fst p) (fst p')
  snr-snd  : {p p' : RTm Γ} → SNRed p p' → SNRed (snd p) (snd p')

-- Head reduction is reduction.
snr→⟶ : {t t' : RTm Γ} → SNRed t t' → t ⟶ t'
snr→⟶ (snr-β {s} {u} _)  = β s u
snr→⟶ (snr-βfst {a} {b} _) = βfst a b
snr→⟶ (snr-βsnd {a} {b} _) = βsnd a b
snr→⟶ (snr-app r)  = ξ-appˡ (snr→⟶ r)
snr→⟶ (snr-fst r)  = ξ-fst (snr→⟶ r)
snr→⟶ (snr-snd r)  = ξ-snd (snr→⟶ r)

------------------------------------------------------------------------
-- 2. The logical relation, over the INDUCTIVE `SN`.
--
-- Identical to `SpikeSNW`'s whnf-carrying shape; only the `SN` changes.
------------------------------------------------------------------------

infix 4 _⊩∋_

data ⊩_ {Γ} : RTy Γ → Set
_⊩∋_ : {Γ : Cx} {A : RTy Γ} → ⊩ A → RTm Γ → Set

data ⊩_ {Γ} where
  ⊩base : {A : RTy Γ} → A ⟶ᵀ* base → ⊩ A
  ⊩U    : {A : RTy Γ} → A ⟶ᵀ* U → ⊩ A
  ⊩ne   : {A : RTy Γ} {n : RTm Γ} → A ⟶ᵀ* El n → SNe n → ⊩ A
  ⊩Π    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
        → A ⟶ᵀ* Π F G
        → (⊩F : ⊩ F)
        → ((u : RTm Γ) → ⊩F ⊩∋ u → ⊩ (subTy (single u) G))
        → ⊩ A

⊩base _     ⊩∋ t = SN t
⊩U _        ⊩∋ t = SN t
⊩ne _ _     ⊩∋ t = SN t
⊩Π _ ⊩F ⊩G  ⊩∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩∋ u) → (⊩G u r) ⊩∋ app t u)

------------------------------------------------------------------------
-- ★ 3. THE WALL, GONE.
--
-- Compare `SpikeSNX` §5: this needed `sn-exp·`, SN closed under head expansion
-- under a spine, and the spine could not even be inverted.  Here the `Π` case
-- is one `snr-app` and a structurally smaller recursive call on `⊩G v rv`.
------------------------------------------------------------------------

exp : {A : RTy Γ} (R : ⊩ A) {t t' : RTm Γ} → SNRed t t' → R ⊩∋ t' → R ⊩∋ t
exp (⊩base _)     r h = sn-exp r h
exp (⊩U _)        r h = sn-exp r h
exp (⊩ne _ _)     r h = sn-exp r h
exp (⊩Π _ ⊩F ⊩G)  r h =
  (sn-exp r (projl h) , λ v rv → exp (⊩G v rv) (snr-app r) (projr h v rv))

------------------------------------------------------------------------
-- 4. Candidate conditions — shorter than the accessibility versions.
--
-- CR3 in particular: `SpikeSNW` needed the auxiliary `sn-app-ne` (a
-- lexicographic induction over two `SN` derivations) to know that a neutral
-- applied to an SN argument stays SN.  Here that IS the constructor `sne-app`,
-- so the lemma disappears.
------------------------------------------------------------------------

CR1 : {A : RTy Γ} (R : ⊩ A) {t : RTm Γ} → R ⊩∋ t → SN t
CR1 (⊩base _)  h = h
CR1 (⊩U _)     h = h
CR1 (⊩ne _ _)  h = h
CR1 (⊩Π _ _ _) h = projl h

CR3 : {A : RTy Γ} (R : ⊩ A) {t : RTm Γ} → SNe t → R ⊩∋ t
CR3 (⊩base _)     nt = sn-ne nt
CR3 (⊩U _)        nt = sn-ne nt
CR3 (⊩ne _ _)     nt = sn-ne nt
CR3 (⊩Π _ ⊩F ⊩G)  nt =
  (sn-ne nt , λ u ru → CR3 (⊩G u ru) (sne-app nt (CR1 ⊩F ru)))

⊩var : {A : RTy Γ} (R : ⊩ A) (x : Var Γ) → R ⊩∋ var x
⊩var R x = CR3 R (sne-var x)

------------------------------------------------------------------------
-- ★ 5. `fund`'s λ-CASE, COMPLETE.
--
-- This is what the whole of W1c/W1d was for.  `snr-β` supplies the head redex,
-- `exp` transports the body's membership across it, and `CR1` extracts the `SN`
-- of the argument that `snr-β` requires.
------------------------------------------------------------------------

sem-lam : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Π F G)
          (⊩F : ⊩ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩∋ u → ⊩ (subTy (single u) G))
          {s : RTm (Γ ∙)} →
          SN s →
          ((u : RTm Γ) (r : ⊩F ⊩∋ u) → (⊩G u r) ⊩∋ subTm (single u) s) →
          (⊩Π p ⊩F ⊩G) ⊩∋ lam s
sem-lam p ⊩F ⊩G sns f =
  (sn-lam sns , λ u r → exp (⊩G u r) (snr-β (CR1 ⊩F r)) (f u r))

-- …and the Π elimination, for completeness (as `SpikeSNX.sem-app`).
sem-app : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Π F G)
          (⊩F : ⊩ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩∋ u → ⊩ (subTy (single u) G))
          {t u : RTm Γ} →
          (⊩Π p ⊩F ⊩G) ⊩∋ t → (r : ⊩F ⊩∋ u) → (⊩G u r) ⊩∋ app t u
sem-app p ⊩F ⊩G h r = projr h _ r

------------------------------------------------------------------------
-- ★ 6. WEAK NORMALIZATION — exactly what `dec-conv` consumes.
--
-- `NbEPDirDBDec.dec-conv` asks for `t ⟶* n` with `IsNormal n`.  That falls out
-- of the inductive presentation by structural recursion: `sn-exp` records a
-- reduction, every other `SN` constructor records a congruence, and `SNe`
-- delivers a NEUTRAL normal form so the `app`/`fst`/`snd` cases can rule out a
-- top-level redex.
--
-- This is why the `SN → Acc` direction never has to be proven.
------------------------------------------------------------------------

IsNormal : RTm Γ → Set
IsNormal t = ∀ {u} → ¬ (t ⟶ u)

-- The normal form is carried together with its own `SN` — every case can
-- produce it, and `wne`'s `app` case NEEDS it (`sne-app` takes `SN` of the
-- argument).  Deriving it instead would require `SN` closed under reduction,
-- which is a real lemma in the JM presentation; carrying it is free.
record WN {Γ} (t : RTm Γ) : Set where
  constructor mkWN
  field
    nfm : RTm Γ
    rd  : t ⟶* nfm
    nrm : IsNormal nfm
    snf : SN nfm

record WNe {Γ} (t : RTm Γ) : Set where
  constructor mkWNe
  field
    nfm : RTm Γ
    rd  : t ⟶* nfm
    nrm : IsNormal nfm
    neu : SNe nfm

open WN
open WNe

wn  : {t : RTm Γ} → SN t → WN t
wne : {t : RTm Γ} → SNe t → WNe t

-- neutral normal forms: a top-level redex is impossible because the head is a
-- variable, so `β`/`βfst`/`βsnd` cannot fire.
wne (sne-var x) = mkWNe (var x) done (λ ()) (sne-var x)
wne (sne-app n u) with wne n | wn u
... | mkWNe n₁ r₁ nm₁ ne₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWNe (app n₁ n₂)
            (⟶*-trans (⟶*-appˡ r₁) (⟶*-appʳ r₂))
            nrm' (sne-app ne₁ sn₂)
  where
    nrm' : IsNormal (app n₁ n₂)
    nrm' (ξ-appˡ q) = nm₁ q
    nrm' (ξ-appʳ q) = nm₂ q
wne (sne-fst n) with wne n
... | mkWNe n₁ r₁ nm₁ ne₁ = mkWNe (fst n₁) (⟶*-fst r₁) nrm' (sne-fst ne₁)
  where
    nrm' : IsNormal (fst n₁)
    nrm' (ξ-fst q) = nm₁ q
wne (sne-snd n) with wne n
... | mkWNe n₁ r₁ nm₁ ne₁ = mkWNe (snd n₁) (⟶*-snd r₁) nrm' (sne-snd ne₁)
  where
    nrm' : IsNormal (snd n₁)
    nrm' (ξ-snd q) = nm₁ q

wn (sn-ne n) with wne n
... | mkWNe n₁ r₁ nm₁ ne₁ = mkWN n₁ r₁ nm₁ (sn-ne ne₁)
wn (sn-lam s) with wn s
... | mkWN n₁ r₁ nm₁ sn₁ = mkWN (lam n₁) (⟶*-lam r₁) nrm' (sn-lam sn₁)
  where
    nrm' : IsNormal (lam n₁)
    nrm' (ξ-lam q) = nm₁ q
wn (sn-pair a b) with wn a | wn b
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (pair n₁ n₂) (⟶*-trans (⟶*-pairˡ r₁) (⟶*-pairʳ r₂)) nrm' (sn-pair sn₁ sn₂)
  where
    nrm' : IsNormal (pair n₁ n₂)
    nrm' (ξ-pairˡ q) = nm₁ q
    nrm' (ξ-pairʳ q) = nm₂ q
wn sn-cb = mkWN ⌜base⌝ done (λ ()) sn-cb
wn (sn-cΠ c d) with wn c | wn d
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (⌜Π⌝ n₁ n₂) (⟶*-trans (⟶*-⌜Π⌝ˡ r₁) (⟶*-⌜Π⌝ʳ r₂)) nrm' (sn-cΠ sn₁ sn₂)
  where
    nrm' : IsNormal (⌜Π⌝ n₁ n₂)
    nrm' (ξ-⌜Π⌝ˡ q) = nm₁ q
    nrm' (ξ-⌜Π⌝ʳ q) = nm₂ q
wn (sn-cΣ c d) with wn c | wn d
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (⌜Σ⌝ n₁ n₂) (⟶*-trans (⟶*-⌜Σ⌝ˡ r₁) (⟶*-⌜Σ⌝ʳ r₂)) nrm' (sn-cΣ sn₁ sn₂)
  where
    nrm' : IsNormal (⌜Σ⌝ n₁ n₂)
    nrm' (ξ-⌜Σ⌝ˡ q) = nm₁ q
    nrm' (ξ-⌜Σ⌝ʳ q) = nm₂ q
-- ★ the head-expansion case: prepend the recorded reduction
wn (sn-exp r h) with wn h
... | mkWN n₁ r₁ nm₁ sn₁ = mkWN n₁ (step (snr→⟶ r) r₁) nm₁ sn₁

-- ★ and hence: every member of every semantic type weakly normalizes — the
-- input `NbEPDirDBDec.dec-conv` is waiting for.
⊩wn : {A : RTy Γ} (R : ⊩ A) {t : RTm Γ} → R ⊩∋ t → WN t
⊩wn R h = wn (CR1 R h)

------------------------------------------------------------------------
-- 7. NON-VACUITY: the inductive `SN` accepts a real β-redex, and `wn`
--    actually computes its normal form.
------------------------------------------------------------------------

-- `(λx. x) y` in a one-variable context.
redexTm : RTm (ε ∙)
redexTm = app (lam (var vz)) (var vz)

-- It is `SN` — by head expansion, the constructor that replaced the lemma.
redexSN : SN redexTm
redexSN = sn-exp (snr-β (sn-ne (sne-var vz))) (sn-ne (sne-var vz))

-- ★ and `wn` computes its normal form on the nose.
redex-nf : WN.nfm (wn redexSN) ≡ var vz
redex-nf = refl

-- The normal form really is normal, and the reduction really reaches it —
-- both are fields of the same record, so `dec-conv` can be fed directly.
redex-red : redexTm ⟶* var vz
redex-red = WN.rd (wn redexSN)
