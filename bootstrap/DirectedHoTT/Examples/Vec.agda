------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — `Vec` AS FORDING SUGAR.  THE ACCEPTANCE TEST for
-- the indexed-descriptions increment (PLAN-INDEXED §3), written under
-- the standing rule: a library is exercised by an EXAMPLE, per branch.
--
-- ★ WHY THIS FILE IS THE POINT.  Everything else about `IMu`/`icon`/
--   `ielim` is a metatheorem ABOUT them.  Nothing anywhere constructed a
--   single `icon` or `ielim`, and that is exactly the shape the `lexrec`
--   failure mode takes: derived, green, and UNCALLABLE.  This file makes
--   the increment callable.
--
--   ⚠ It is also where the DESIGN is tested rather than the proofs: §9.2
--   generalised `iρ` precisely so `cons`'s recursive field can sit at an
--   EARLIER FIELD, and §10 restricted `iκ`'s code precisely so a FORDING
--   constraint is the one thing that may mention the index.  `consWf`
--   below uses both, and neither has any other customer.
--
--        nil  : (n ≡ zero)                        → Vec n
--        cons : (m : Nat) → Nat → Vec m → (n ≡ suc m) → Vec n
--
-- ★ WHAT IS DEMONSTRATED, in order:
--     · `VecWf`      — the description is well-formed (`iwf-ρ` at an
--                      earlier field; `icw-clo` and `icw-ford`);
--     · `⊢vnil` / `⊢vcons` — the constructors TYPE (`⊢icon`);
--     · `⊢vlen`    — an eliminator TYPES (`⊢ielim`), at the
--                      index-quantified methods §9.1 forced;
--     · `vlen-nil` / `vlen-cons` — and it COMPUTES: ι fires.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Vec where
open import normalizer.Syntax.Types using ( _≡_; refl; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; U; El; Π; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; app; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜Id⌝; idrefl; icon; ielim
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ilookupD; _∈ID_; hereID; thereID
        ; ipayTy; isingle; iext; ifields; sel
        ; renTy; renTm; subTy; subTm )
open import DirectedHoTT.Metatheory.Canonicity
  using ( idEndpoints; zero≇suc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-appˡ; ξ-fst; ξ-snd; ξ-nsuc
        ; ξ-ielimⁱ; ξ-ielimᵗ
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ; _≅_
        ; _⟶ᵀ_; El-⌜Nat⌝; El-⌜Id⌝
        ; ι-ielim
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢conv
        ; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢idrefl
        ; ⊢icon; ⊢ielim
        ; _⊢ty_; ty-U; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTy )

------------------------------------------------------------------------
-- 0. The index type, and the two conversions everything below rides.
--
-- ⚠ `I = El ⌜Nat⌝`, not `Nat`.  `⊢⌜Id⌝` wants its endpoints at `El c`,
--   and the FORDING constraint's endpoints ARE the index — so taking the
--   index type to be the DECODE of a code removes a conversion from
--   every single obligation below.  `εwkTy (El ⌜Nat⌝) = El ⌜Nat⌝`
--   definitionally, `⌜Nat⌝` being closed.
------------------------------------------------------------------------

INat : RTy ε
INat = El ⌜Nat⌝

-- `El ⌜Nat⌝ ≅ᵀ Nat`, both ways.  One step, used everywhere.
elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = credᵀ El-⌜Nat⌝

-- a `Nat` term, read as an index
toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ elNat)

-- …and back
fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d elNat

------------------------------------------------------------------------
-- 1. THE DESCRIPTION.
--
-- ⚠ READ THE DE BRUIJN INDICES — they are the content.  A constructor
--   starts in `ε ∙` (the AMBIENT INDEX alone) and gains one slot per
--   field, so inside `cons`'s constraint the ambient index has been
--   pushed out to `vs (vs (vs vz))` while `m` sits at `vs (vs vz)`.
--   THAT is what §9.2 bought: the constraint and the recursive field can
--   both name an earlier field.
------------------------------------------------------------------------

-- nil : (n ≡ zero) → Vec n
nilC : ICon (ε ∙)
nilC = iκ (⌜Id⌝ ⌜Nat⌝ (var vz) nzero) iι

-- cons : (m : Nat) → Nat → Vec m → (n ≡ suc m) → Vec n
consC : ICon (ε ∙)
consC =
  iκ ⌜Nat⌝                                        -- m
    (iκ ⌜Nat⌝                                     -- the element
      (iρ (var (vs vz))                           -- Vec m  ← THE EARLIER FIELD
        (iκ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs (vs vz))))   -- n
                        (nsuc (var (vs (vs vz)))))-- suc m
          iι)))

VecD : IDesc
VecD = nilC ◂ (consC ◂ inil)

Vec : {Γ : Cx} → RTm Γ → RTy Γ
Vec n = IMu VecD INat n

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS — where `icw-clo` and `icw-ford` earn their keep.
------------------------------------------------------------------------

nilWf : IConWf VecD INat (◇ ▹ INat) nilC
nilWf =
  iwf-κ (⌜Id⌝ ⌜Nat⌝ (var vz) nzero)
        (icw-ford ⌜Nat⌝ (var vz) nzero)
        (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI ⊢nzero))
        iwf-ι

consWf : IConWf VecD INat (◇ ▹ INat) consC
consWf =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
   (iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
    (iwf-ρ (var (vs vz)) (⊢var (there here))
     (iwf-κ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs (vs vz)))) (nsuc (var (vs (vs vz)))))
            (icw-ford ⌜Nat⌝ (var (vs (vs (vs vz)))) (nsuc (var (vs (vs vz)))))
            (⊢⌜Id⌝ ⊢⌜Nat⌝
                   (⊢var (there (there (there here))))
                   (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
            iwf-ι)))

VecWf : IDescWf INat VecD
VecWf = idwf-cons nilWf (idwf-cons consWf idwf-nil)

------------------------------------------------------------------------
-- 3. THE CONSTRUCTORS — `⊢icon`, twice.
--
-- ⚠ THE PAYLOAD IS THE Σ-CHAIN `ipayTy` COMPUTES, constraint field and
--   all.  `nil`'s is `Σ' (El (⌜Id⌝ ⌜Nat⌝ n nzero)) Unit` — Fording is not
--   a comment here, it is a component you have to supply.
------------------------------------------------------------------------

vnil : {Γ : Cx} → RTm Γ
vnil = icon zero (pair (idrefl ⌜Nat⌝ nzero) unit)

-- the Fording witness at `n := zero`: `El (⌜Id⌝ ⌜Nat⌝ zero zero)`
reflZ : {Γ : Ctx} → Γ ⊢ idrefl ⌜Nat⌝ nzero ∷ El (⌜Id⌝ ⌜Nat⌝ nzero nzero)
reflZ = ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI ⊢nzero))
              (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ nzero nzero)))

⊢vnil : ◇ ⊢ vnil ∷ Vec nzero
⊢vnil =
  ⊢icon VecWf hereID (toI ⊢nzero)
        (⊢pair ty-Unit reflZ ⊢unit)

-- ★ CONS, at a CONCRETE index.  ⚠ deliberately concrete: with `m` a
--   numeral every weakening in the payload's Σ-chain computes away, and
--   what is left to supply is exactly the interesting part — the
--   RECURSIVE field and the FORDING constraint.  A `⊢vcons` general in
--   `m` needs the weakening plumbing and demonstrates nothing more.
vcons : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
vcons m a xs =
  icon (suc zero)
       (pair m (pair a (pair xs (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))

-- the Fording witness at `n := suc zero`, `m := zero`
reflSZ : {Γ : Ctx} →
         Γ ⊢ idrefl ⌜Nat⌝ (nsuc nzero) ∷
             El (⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc nzero))
reflSZ = ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero)))
               (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc nzero))))

-- `[0] : Vec 1`
v1 : {Γ : Cx} → RTm Γ
v1 = vcons nzero nzero vnil

-- the three `⊢ty` premises `⊢pair` asks for, each stated where it is
-- needed.  ⚠ each is at ONE binder over the ambient: the Σ-chain is
-- consumed head-first, so every step substitutes its binder away.
tyFord : {Γ : Ctx} →
         Γ ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc nzero))) Unit
tyFord = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero)) (toI (⊢nsuc ⊢nzero))))
              ty-Unit

tyRec : {Γ : Ctx} →
        Γ ⊢ty Σ' (IMu VecD INat nzero)
                 (Σ' (El (⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc nzero))) Unit)
tyRec = ty-Σ (ty-IMu VecWf (toI ⊢nzero)) tyFord

-- …and the UNSUBSTITUTED tail, the one that still mentions `m`.
tyP₁ : (◇ ▹ El ⌜Nat⌝) ⊢ty
       Σ' (El ⌜Nat⌝)
          (Σ' (IMu VecD INat (var (vs vz)))
              (Σ' (El (⌜Id⌝ ⌜Nat⌝ (nsuc nzero)
                                  (nsuc (var (vs (vs vz)))))) Unit))
tyP₁ =
  ty-Σ (ty-El ⊢⌜Nat⌝)
    (ty-Σ (ty-IMu VecWf (⊢var (there here)))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero))
                          (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
            ty-Unit))

⊢v1 : ◇ ⊢ v1 ∷ Vec (nsuc nzero)
⊢v1 =
  ⊢icon VecWf (thereID hereID) (toI (⊢nsuc ⊢nzero))
    (⊢pair tyP₁ (toI ⊢nzero)
      (⊢pair tyRec (toI ⊢nzero)
        (⊢pair tyFord ⊢vnil
          (⊢pair ty-Unit reflSZ ⊢unit))))

------------------------------------------------------------------------
-- 4. THE ELIMINATOR — `⊢ielim`, and it COMPUTES.
--
-- `vlen : Vec n → Nat`, at the CONSTANT motive `Nat`.  ⚠ constant on
-- purpose: `iinst i t Nat = Nat` and `iatCon k i Nat = Nat` definitionally,
-- so what is left to supply is exactly the thing §9.1 forced — a method
-- that QUANTIFIES OVER THE INDEX (the outer `lam`), which is what lets
-- ONE method tuple serve `cons`'s recursive call at `m` and the ambient
-- call at `suc m` alike.
------------------------------------------------------------------------

-- λ n. λ p. λ ih. zero
mnil : {Γ : Cx} → RTm Γ
mnil = lam (lam (lam nzero))

-- λ n. λ p. λ ih. suc (fst ih)
mcons : {Γ : Cx} → RTm Γ
mcons = lam (lam (lam (nsuc (fst (var vz)))))

vms : {Γ : Cx} → RTm Γ
vms = pair mnil (pair mcons unit)

vlen : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
vlen n v = ielim VecD n vms v

-- the payload types, as `⊢ty` derivations under the method's index binder
tyPayNil : {Γ : Ctx} → (Γ ▹ El ⌜Nat⌝) ⊢ty
           Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) nzero)) Unit
tyPayNil = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI ⊢nzero))) ty-Unit

tyPayCons : {Γ : Ctx} → (Γ ▹ El ⌜Nat⌝) ⊢ty
            Σ' (El ⌜Nat⌝)
               (Σ' (El ⌜Nat⌝)
                  (Σ' (IMu VecD INat (var (vs vz)))
                     (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs (vs vz))))
                                         (nsuc (var (vs (vs vz)))))) Unit)))
tyPayCons =
  ty-Σ (ty-El ⊢⌜Nat⌝)
    (ty-Σ (ty-El ⊢⌜Nat⌝)
      (ty-Σ (ty-IMu VecWf (⊢var (there here)))
        (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (⊢var (there (there (there here))))
                            (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
              ty-Unit)))

⊢mnil : {Γ : Ctx} → Γ ⊢ mnil ∷ Π (El ⌜Nat⌝)
                       (Π (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) nzero)) Unit)
                          (Π Unit Nat))
⊢mnil = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam tyPayNil (⊢lam ty-Unit ⊢nzero))

⊢mcons : {Γ : Ctx} → Γ ⊢ mcons ∷
         Π (El ⌜Nat⌝)
           (Π (Σ' (El ⌜Nat⌝)
                 (Σ' (El ⌜Nat⌝)
                    (Σ' (IMu VecD INat (var (vs vz)))
                       (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs (vs vz))))
                                           (nsuc (var (vs (vs vz)))))) Unit))))
              (Π (Σ' Nat Unit) Nat))
⊢mcons =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayCons
      (⊢lam (ty-Σ ty-Nat ty-Unit) (⊢nsuc (⊢fst (⊢var here)))))

⊢vms : ◇ ⊢ vms ∷ imethsTy VecD INat Nat VecD
⊢vms =
  ⊢pair (ty-Σ (ty-Π (ty-El ⊢⌜Nat⌝)
                    (ty-Π tyPayCons (ty-Π (ty-Σ ty-Nat ty-Unit) ty-Nat)))
              ty-Unit)
        ⊢mnil
        (⊢pair ty-Unit ⊢mcons ⊢unit)

-- ★★ AND THE ELIMINATOR TYPES.
⊢vlen : ◇ ⊢ vlen (nsuc nzero) v1 ∷ Nat
⊢vlen = ⊢ielim VecWf ty-Nat (toI (⊢nsuc ⊢nzero)) ⊢vms ⊢v1

⊢vlen0 : ◇ ⊢ vlen nzero vnil ∷ Nat
⊢vlen0 = ⊢ielim VecWf ty-Nat (toI ⊢nzero) ⊢vms ⊢vnil

------------------------------------------------------------------------
-- 5. …AND IT COMPUTES.  ι fires — which is the whole difference between
--    "proven about" and "callable".
------------------------------------------------------------------------

vlen-nil-fires :
  {Γ : Cx} →
  vlen {Γ} nzero vnil ⟶
    ifields VecD nzero vms (isingle nzero)
      (ilookupD VecD zero)
      (sel zero vms)
      (pair (idrefl ⌜Nat⌝ nzero) unit)
vlen-nil-fires = ι-ielim VecD nzero vms zero (pair (idrefl ⌜Nat⌝ nzero) unit)

-- ★★★ THE WHOLE CHAIN.  `length []` really is `0`: ι fires, `sel`
--   projects the method out of the tuple, and the three β's are the
--   INDEX, the payload and the (empty) IH tuple — the three binders
--   §9.1's `imethTy` introduced.
vlen-nil : {Γ : Cx} → vlen {Γ} nzero vnil ⟶* nzero
vlen-nil =
  step (ι-ielim VecD nzero vms zero (pair (idrefl ⌜Nat⌝ nzero) unit))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst mnil (pair mcons unit)))))
  (step (ξ-appˡ (ξ-appˡ (β (lam (lam nzero)) nzero)))
  (step (ξ-appˡ (β (lam nzero) (pair (idrefl ⌜Nat⌝ nzero) unit)))
  (step (β nzero unit) done))))

-- the cons payload and its tails, named so the projections' β-steps can
-- be written down (⚠ `fst`/`snd` are TERM FORMERS here, not projections:
-- `fst (pair a b)` reduces by `βfst`, it is not definitionally `a`).
cP4 cP3 cP2 cP1 : {Γ : Cx} → RTm Γ
cP4 = pair (idrefl ⌜Nat⌝ (nsuc nzero)) unit
cP3 = pair vnil cP4
cP2 = pair nzero cP3
cP1 = pair nzero cP2

nsucStar : {Γ : Cx} {t u : RTm Γ} → t ⟶* u → nsuc t ⟶* nsuc u
nsucStar done       = done
nsucStar (step r q) = step (ξ-nsuc r) (nsucStar q)

-- ★★★ AND THE RECURSIVE ONE.  `length [0]` is `1`, and the middle of
--   this chain is where the whole indexed design shows up at once:
--   `iihs` built the IH tuple by calling `ielim` AGAIN at the recursive
--   field's OWN index — `fst cP1`, i.e. `m`, NOT the ambient `suc m` —
--   with the SAME method tuple.  That is precisely what PLAN-INDEXED
--   §9.1's index-quantified `imethTy` exists to make typable and what
--   §9.2's telescope makes expressible.  Everything after it is the
--   projections β-firing.
vlen-cons : {Γ : Cx} → vlen {Γ} (nsuc nzero) v1 ⟶* nsuc nzero
vlen-cons =
  step (ι-ielim VecD (nsuc nzero) vms (suc zero) cP1)
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-fst (βsnd mnil (pair mcons unit))))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst mcons unit))))
  (step (ξ-appˡ (ξ-appˡ (β (lam (lam (nsuc (fst (var vz))))) (nsuc nzero))))
  (step (ξ-appˡ (β (lam (nsuc (fst (var vz)))) cP1))
  (step (β (nsuc (fst (var vz)))
           (pair (ielim VecD (fst cP1) vms (fst (snd (snd cP1)))) unit))
  (step (ξ-nsuc (βfst (ielim VecD (fst cP1) vms (fst (snd (snd cP1)))) unit))
  (step (ξ-nsuc (ξ-ielimⁱ (βfst nzero cP2)))
  (step (ξ-nsuc (ξ-ielimᵗ (ξ-fst (ξ-snd (βsnd nzero cP2)))))
  (step (ξ-nsuc (ξ-ielimᵗ (ξ-fst (βsnd nzero cP3))))
  (step (ξ-nsuc (ξ-ielimᵗ (βfst vnil cP4)))
    (nsucStar vlen-nil)))))))))))

------------------------------------------------------------------------
-- 6. ★★★ WHAT FORDING BUYS — `⊢icon`'s note, at this description.
--
-- `nil` and `cons` are BOTH available at EVERY index — that is what `iι`
-- means, and it is why `IMuMem` is uniform in the index (PLAN-INDEXED
-- §2).  What rules the bad ones out is the CONSTRAINT FIELD, and here is
-- that claim as a THEOREM rather than a comment: there is no closed
-- `cons` payload at index `zero`.
--
-- The mechanism is `Canonicity.idEndpoints` — a closed proof of `Id`
-- forces its endpoints CONVERTIBLE.  A `cons` payload's last component
-- inhabits `El (⌜Id⌝ ⌜Nat⌝ zero (suc m))`, which decodes to
-- `Id (El ⌜Nat⌝) zero (suc m)`; `idEndpoints` turns it into
-- `zero ≅ suc m`, and `zero≇suc` closes it.
------------------------------------------------------------------------

-- ★★★ NO `cons` PAYLOAD LIVES AT INDEX ZERO.
no-cons-at-zero :
  {m a xs : RTm ε} →
  ◇ ⊢ pair m (pair a (pair xs (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))
        ∷ ipayTy VecD INat (isingle nzero) (ilookupD VecD (suc zero)) → ⊥
no-cons-at-zero dp =
  zero≇suc (idEndpoints
    (⊢conv (⊢fst (⊢snd (⊢snd (⊢snd dp)))) (credᵀ (El-⌜Id⌝ _ _ _))))
