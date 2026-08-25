------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — DOGFOODING, step 5 of PLAN-INDEXED §5:
-- ★★★ A SYNTAX AS AN INDEXED DESCRIPTION, inside the kernel.
--
-- The λ-calculus, scoped by CONTEXT DEPTH:
--
--        var : Fin n      → Tm n          ← §12, a NESTED FAMILY
--        lam : Tm (suc n) → Tm n          ← THE POINT
--        app : Tm n → Tm n → Tm n
--
-- ★ WHY THIS AND NOT `Vec`.  `Vec` exercises `iρ` at an EARLIER FIELD
--   (PLAN-INDEXED §9.2).  It does NOT exercise the thing indexed
--   descriptions were introduced for in the first place — §1's table:
--
--     | | `RTm`'s shape | `Vec` |
--     | what varies | the FIELD's index (`lam` goes under a binder) | the TARGET index |
--
--   `lam`'s recursive field sits at `suc` of the AMBIENT index.  Nothing
--   in the development did that until this file.  It is the whole
--   content of "`RTm` relates `Γ` to `Γ` or `Γ ∙`, never downward", and
--   it is why `iι` (an ambient target) plus a shifted `iρ` is enough for
--   a syntax while `Vec` needs Fording.
--
-- ★★★ `var` CARRIES A `Fin n`, and that is the SECOND thing this file
--   exercises.  It was a bare `Nat` until §12: a field's type is a κ
--   CODE, and `ICodeWf` admitted only CLOSED codes (`icw-clo`) and
--   FORDING constraints (`icw-ford`).  Neither can say "this field is
--   an inductive FAMILY at the ambient index".  `icw-imu` can, and §0.5
--   below is what it buys.
--
-- ⚠ THE REJECTED ALTERNATIVE, kept because it is a real constraint and
--   not a preference: an ORDER constraint `⌜Hom⌝ ⌜Nat⌝ ⟨i⟩ ⟨n⟩` CANNOT
--   be an `ICodeWf` row.  `⊩₀Hom` needs the `Hom` to be STUCK, and
--   `Hom Nat a b` COMPUTES — so it is not reduction-determined at an
--   arbitrary environment.  That is why §10 excluded `⌜Hom⌝`, and it is
--   why scope-safety had to arrive as a NESTED FAMILY rather than as a
--   bound.  Fording gets `Fin` its own target index; only `icw-imu`
--   gets `Fin` into `var`'s field.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Scoped where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; U; El; Π; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; app; pair; fst; snd; unit; nzero; nsuc; natrec
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; idrefl; icon; ielim
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ilookupD; _∈ID_; hereID; thereID
        ; ipayTy; isingle; iext; ifields; sel
        ; renTy; renTm; subTy; subTm )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; wk-single
        ; _∋_∷_; here; there
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-appˡ; ξ-fst; ξ-snd; ξ-nsuc
        ; ξ-ielimⁱ; ξ-ielimᵗ; ι-ielim
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; _⟶ᵀ_; El-⌜Nat⌝; El-⌜Id⌝; El-⌜IMu⌝
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢conv
        ; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢idrefl; ⊢natrec
        ; ⊢icon; ⊢ielim
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTy )

------------------------------------------------------------------------
-- 0. The index: CONTEXT DEPTH.  `Cx` is unary (`ε`/`_∙`), so a context
--    IS its length, and the object-language index type is `Nat`.
--
-- ⚠ `El ⌜Nat⌝`, not `Nat` — same reason as `Examples/Vec`: taking the
--   index type to be the DECODE of a code removes a conversion from
--   every `ty-IMu` obligation.
------------------------------------------------------------------------

INat : RTy ε
INat = El ⌜Nat⌝

elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = credᵀ El-⌜Nat⌝

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ elNat)

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d elNat

------------------------------------------------------------------------
-- 0.5 ★★★ `Fin` — A NESTED INDEXED FAMILY, and what §12's `icw-imu`
--     was added for.
--
--        fzero : (m : Nat) →           n ≡ suc m → Fin n
--        fsuc  : (m : Nat) → Fin m  →  n ≡ suc m → Fin n
--
-- ⚠ FORDED, exactly like `Vec` — `iι` targets the AMBIENT index, so a
--   constructor that wants to land at `suc m` must SAY SO with an `Id`
--   field.  Note what that does and does not settle: Fording gives
--   `Fin` its own TARGET index.  It cannot give `var` a FIELD of type
--   `Fin n`, because a field's type is a κ CODE and Fording produces a
--   CONSTRAINT.  Both mechanisms appear below, one line apart, doing
--   different jobs — which is the cleanest statement of why §12 is not
--   redundant with §10.
------------------------------------------------------------------------

fzeroC : ICon (ε ∙)
fzeroC = iκ ⌜Nat⌝ (iκ (⌜Id⌝ ⌜Nat⌝ (var (vs vz)) (nsuc (var vz))) iι)

fsucC : ICon (ε ∙)
fsucC =
  iκ ⌜Nat⌝
   (iρ (var vz)
    (iκ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) (nsuc (var (vs vz)))) iι))

FinD : IDesc
FinD = fzeroC ◂ (fsucC ◂ inil)

Fin : {Γ : Cx} → RTm Γ → RTy Γ
Fin n = IMu FinD INat n

fzeroWf : IConWf FinD INat (◇ ▹ INat) fzeroC
fzeroWf =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
   (iwf-κ (⌜Id⌝ ⌜Nat⌝ (var (vs vz)) (nsuc (var vz)))
          (icw-ford ⌜Nat⌝ (var (vs vz)) (nsuc (var vz)))
          (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there here))
                        (toI (⊢nsuc (fromI (⊢var here)))))
          iwf-ι)

fsucWf : IConWf FinD INat (◇ ▹ INat) fsucC
fsucWf =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
   (iwf-ρ (var vz) (⊢var here)
    (iwf-κ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) (nsuc (var (vs vz))))
           (icw-ford ⌜Nat⌝ (var (vs (vs vz))) (nsuc (var (vs vz))))
           (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there here)))
                         (toI (⊢nsuc (fromI (⊢var (there here))))))
           iwf-ι))

FinWf : IDescWf INat FinD
FinWf = idwf-cons fzeroWf (idwf-cons fsucWf idwf-nil)

-- `El (⌜IMu⌝ FinD INat n) ≅ᵀ Fin n` — the ONE conversion a κ field of
-- family type costs, and the exact mirror of `elNat`.
elFin : {Γ : Cx} {n : RTm Γ} → El (⌜IMu⌝ FinD INat n) ≅ᵀ Fin n
elFin = credᵀ El-⌜IMu⌝

toFin : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
        Γ ⊢ k ∷ Fin n → Γ ⊢ k ∷ El (⌜IMu⌝ FinD INat n)
toFin d = ⊢conv d (csymᵀ elFin)

-- `fz : Fin 1` — the de Bruijn variable `0`, at depth 1.  Concrete for
-- `Examples/Vec`'s reason: with the index a numeral the payload's
-- weakenings compute away and only the interesting fields remain.
fz : {Γ : Cx} → RTm Γ
fz = icon zero (pair nzero (pair (idrefl ⌜Nat⌝ (nsuc nzero)) unit))

reflS1 : {Γ : Ctx} →
         Γ ⊢ idrefl ⌜Nat⌝ (nsuc nzero) ∷
             El (⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc nzero))
reflS1 = ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero)))
               (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc nzero))))

tyFz : (◇ ▹ El ⌜Nat⌝) ⊢ty
       Σ' (El (⌜Id⌝ ⌜Nat⌝ (nsuc nzero) (nsuc (var vz)))) Unit
tyFz = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero))
                           (toI (⊢nsuc (fromI (⊢var here))))))
            ty-Unit

⊢fz : ◇ ⊢ fz ∷ Fin (nsuc nzero)
⊢fz = ⊢icon FinWf hereID (toI (⊢nsuc ⊢nzero))
        (⊢pair tyFz (toI ⊢nzero) (⊢pair ty-Unit reflS1 ⊢unit))

------------------------------------------------------------------------
-- 1. THE DESCRIPTION.
--
-- ⚠ In `ICon (ε ∙)` the AMBIENT INDEX is `var vz`, and each field pushes
--   it out by one.  That is the whole reading of the de Bruijn numbers
--   below.
------------------------------------------------------------------------

-- ★★★ var : Fin n → Tm n — a κ field whose CODE IS A FAMILY, at the
--   AMBIENT index.  This is `icw-imu`'s use site, and the reason it is
--   the first forced step toward `RTm` itself: `RTm`'s own fields are
--   `RTy`s and `Desc`s, i.e. other members of the same mutual knot, and
--   no amount of Fording turns a field's TYPE into a family.
varC : ICon (ε ∙)
varC = iκ (⌜IMu⌝ FinD INat (var vz)) iι

-- ★★★ lam : Tm (suc n) → Tm n — THE BINDING SHAPE.
--   The recursive field's index is `suc` OF THE AMBIENT INDEX.  This is
--   the row `Vec` has no analogue of.
lamC : ICon (ε ∙)
lamC = iρ (nsuc (var vz)) iι

-- app : Tm n → Tm n → Tm n — two recursive fields, both at the AMBIENT
--   index.  ⚠ the second one's index is `var (vs vz)`: the first field
--   has already pushed the ambient out by one.
appC : ICon (ε ∙)
appC = iρ (var vz) (iρ (var (vs vz)) iι)

TmD : IDesc
TmD = varC ◂ (lamC ◂ (appC ◂ inil))

Tm : {Γ : Cx} → RTm Γ → RTy Γ
Tm n = IMu TmD INat n

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.
------------------------------------------------------------------------

varWf : IConWf TmD INat (◇ ▹ INat) varC
varWf = iwf-κ (⌜IMu⌝ FinD INat (var vz))
              (icw-imu (var vz) FinWf)
              (⊢⌜IMu⌝ FinWf (⊢var here))
              iwf-ι

-- ⚠ the ONE obligation that is new here: the shifted index must TYPE.
--   `nsuc ⟨n⟩ ∷ El ⌜Nat⌝` — which is why the index type being a decode
--   pays off, and why `Nat` had to be in `U` (stage C) before a syntax
--   could be described at all.
lamWf : IConWf TmD INat (◇ ▹ INat) lamC
lamWf = iwf-ρ (nsuc (var vz)) (toI (⊢nsuc (fromI (⊢var here)))) iwf-ι

appWf : IConWf TmD INat (◇ ▹ INat) appC
appWf = iwf-ρ (var vz) (⊢var here)
         (iwf-ρ (var (vs vz)) (⊢var (there here)) iwf-ι)

TmWf : IDescWf INat TmD
TmWf = idwf-cons varWf (idwf-cons lamWf (idwf-cons appWf idwf-nil))

------------------------------------------------------------------------
-- 3. THE TERM FORMERS — `⊢icon`, three times.
--
-- ⚠ `⊢tapp` needs the ambient index WEAKENED past the first recursive
--   field's binder (`renTm vs n`), because `ipayTy`'s tail lives under
--   the `Σ'`.  `⊢wk` is exactly that, and it is the only place this file
--   needs it — `Vec` never did, because Vec's later fields refer to
--   EARLIER FIELDS rather than to the ambient index.
------------------------------------------------------------------------

tvar : {Γ : Cx} → RTm Γ → RTm Γ
tvar k = icon zero (pair k unit)

tlam : {Γ : Cx} → RTm Γ → RTm Γ
tlam b = icon (suc zero) (pair b unit)

tapp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tapp f a = icon (suc (suc zero)) (pair f (pair a unit))

⊢tvar : {n k : RTm ε} →
        ◇ ⊢ n ∷ El ⌜Nat⌝ → ◇ ⊢ k ∷ Fin n → ◇ ⊢ tvar k ∷ Tm n
⊢tvar dn dk = ⊢icon TmWf hereID dn (⊢pair ty-Unit (toFin dk) ⊢unit)

-- ★★★ THE BINDING CONSTRUCTOR.  Its recursive field is at `suc n`.
⊢tlam : {n b : RTm ε} →
        ◇ ⊢ n ∷ El ⌜Nat⌝ → ◇ ⊢ b ∷ Tm (nsuc n) → ◇ ⊢ tlam b ∷ Tm n
⊢tlam dn db = ⊢icon TmWf (thereID hereID) dn (⊢pair ty-Unit db ⊢unit)

⊢tapp : {n f a : RTm ε} →
        ◇ ⊢ n ∷ El ⌜Nat⌝ → ◇ ⊢ f ∷ Tm n → ◇ ⊢ a ∷ Tm n →
        ◇ ⊢ tapp f a ∷ Tm n
⊢tapp {n = n} dn df da =
  ⊢icon TmWf (thereID (thereID hereID)) dn
    (⊢pair (ty-Σ (ty-IMu TmWf (⊢wk dn)) ty-Unit) df
      (⊢pair ty-Unit
        -- ⚠ the second field's index is `renTm vs n` SUBSTITUTED at the
        --   first field — `wk-single` is the one cast this costs.
        (subst (λ z → ◇ ⊢ _ ∷ IMu TmD INat z) (sym (wk-single n)) da)
        ⊢unit))

-- `λ x. x` at depth 0 — the smallest term that USES the shift.
idTm : {Γ : Cx} → RTm Γ
idTm = tlam (tvar fz)

-- ⚠ THE SCOPE CHECK IS NOW IN THE TYPE.  The bound occurrence sits at
--   depth `suc zero`, so its `Fin` must be `Fin 1` — `⊢fz` is, and no
--   `Fin 0` inhabitant could be supplied in its place.
⊢idTm : ◇ ⊢ idTm ∷ Tm nzero
⊢idTm = ⊢tlam (toI ⊢nzero) (⊢tvar (toI (⊢nsuc ⊢nzero)) ⊢fz)

------------------------------------------------------------------------
-- 4. AN ELIMINATOR OVER THE SYNTAX — `size : Tm n → Nat`.
--
-- Constant motive `Nat`, so `iinst i t Nat = Nat` definitionally and
-- what is left is the part §9.1 forced: a method QUANTIFIED OVER THE
-- INDEX.  Here that binder is load-bearing in a way `Vec` could not show
-- — `lam`'s IH is the recursor run at `suc n`, a DIFFERENT index from
-- the one the method was reached at.
------------------------------------------------------------------------

msize-var msize-lam msize-app msize : {Γ : Cx} → RTm Γ
msize-var = lam (lam (lam (nsuc nzero)))
msize-lam = lam (lam (lam (nsuc (fst (var vz)))))
msize-app = lam (lam (lam (nsuc (plusTm (fst (var vz)) (fst (snd (var vz)))))))
msize     = pair msize-var (pair msize-lam (pair msize-app unit))

size : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
size n t = ielim TmD n msize t

-- the three payload types, under the method's index binder
tyPayVar : {Γ : Ctx} →
           (Γ ▹ El ⌜Nat⌝) ⊢ty Σ' (El (⌜IMu⌝ FinD INat (var vz))) Unit
tyPayVar = ty-Σ (ty-El (⊢⌜IMu⌝ FinWf (⊢var here))) ty-Unit

tyPayLam : {Γ : Ctx} →
           (Γ ▹ El ⌜Nat⌝) ⊢ty Σ' (IMu TmD INat (nsuc (var vz))) Unit
tyPayLam = ty-Σ (ty-IMu TmWf (toI (⊢nsuc (fromI (⊢var here))))) ty-Unit

tyPayApp : {Γ : Ctx} →
           (Γ ▹ El ⌜Nat⌝) ⊢ty
           Σ' (IMu TmD INat (var vz))
              (Σ' (IMu TmD INat (var (vs vz))) Unit)
tyPayApp = ty-Σ (ty-IMu TmWf (⊢var here))
             (ty-Σ (ty-IMu TmWf (⊢var (there here))) ty-Unit)

⊢msize-var : {Γ : Ctx} →
             Γ ⊢ msize-var ∷
             Π (El ⌜Nat⌝)
               (Π (Σ' (El (⌜IMu⌝ FinD INat (var vz))) Unit) (Π Unit Nat))
⊢msize-var = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam tyPayVar (⊢lam ty-Unit (⊢nsuc ⊢nzero)))

⊢msize-lam : {Γ : Ctx} →
             Γ ⊢ msize-lam ∷
             Π (El ⌜Nat⌝)
               (Π (Σ' (IMu TmD INat (nsuc (var vz))) Unit)
                  (Π (Σ' Nat Unit) Nat))
⊢msize-lam =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayLam
      (⊢lam (ty-Σ ty-Nat ty-Unit) (⊢nsuc (⊢fst (⊢var here)))))

⊢msize-app : {Γ : Ctx} →
             Γ ⊢ msize-app ∷
             Π (El ⌜Nat⌝)
               (Π (Σ' (IMu TmD INat (var vz))
                      (Σ' (IMu TmD INat (var (vs vz))) Unit))
                  (Π (Σ' Nat (Σ' Nat Unit)) Nat))
⊢msize-app =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayApp
      (⊢lam (ty-Σ ty-Nat (ty-Σ ty-Nat ty-Unit))
        (⊢nsuc (⊢plus (⊢fst (⊢var here)) (⊢fst (⊢snd (⊢var here)))))))

-- ⚠ CONTEXT-GENERIC, and not decoratively so.  `AmTΠ`'s measure premise
--   is `dm : (Δ ▹ A) ⊢ m ∷ Nat` — the measure is typed UNDER the carrier's
--   binder, never at `◇`.  Both assembled forms were pinned at `◇` while
--   every component below was already `{Γ : Ctx}`-generic; generalising
--   them is a signature change, not a proof.  Use site: `Examples/AmrecIMu`.
⊢msize : {Γ : Ctx} → Γ ⊢ msize ∷ imethsTy TmD INat Nat TmD
⊢msize =
  ⊢pair (ty-Σ (ty-Π (ty-El ⊢⌜Nat⌝)
                    (ty-Π tyPayLam (ty-Π (ty-Σ ty-Nat ty-Unit) ty-Nat)))
              (ty-Σ (ty-Π (ty-El ⊢⌜Nat⌝)
                          (ty-Π tyPayApp
                                (ty-Π (ty-Σ ty-Nat (ty-Σ ty-Nat ty-Unit))
                                      ty-Nat)))
                    ty-Unit))
        ⊢msize-var
        (⊢pair (ty-Σ (ty-Π (ty-El ⊢⌜Nat⌝)
                           (ty-Π tyPayApp
                                 (ty-Π (ty-Σ ty-Nat (ty-Σ ty-Nat ty-Unit))
                                       ty-Nat)))
                     ty-Unit)
               ⊢msize-lam
               (⊢pair ty-Unit ⊢msize-app ⊢unit))

⊢size : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ size n t ∷ Nat
⊢size dn dt = ⊢ielim TmWf ty-Nat dn ⊢msize dt

------------------------------------------------------------------------
-- 5. ★★★ …AND IT RUNS UNDER THE BINDER.
--
-- `size 0 (λx. x) ⟶* 2`.  Step 7→8 is the whole point of the increment:
-- `iihs` built the IH tuple by calling `ielim` again at
--
--        subTm (isingle 0) (nsuc (var vz))  =  suc 0
--
-- — the SHIFTED index, not the ambient one, with the SAME method tuple.
-- `Vec`'s recursive call goes to an earlier FIELD; this one goes to a
-- FUNCTION OF THE AMBIENT INDEX, which is the row PLAN-INDEXED §1 says a
-- syntax needs and `Vec` does not have.
------------------------------------------------------------------------

lamPay varPay : {Γ : Cx} → RTm Γ
lamPay = pair (tvar fz) unit
varPay = pair fz unit

msTail : {Γ : Cx} → RTm Γ
msTail = pair msize-lam (pair msize-app unit)

nsucStar : {Γ : Cx} {t u : RTm Γ} → t ⟶* u → nsuc t ⟶* nsuc u
nsucStar done       = done
nsucStar (step r q) = step (ξ-nsuc r) (nsucStar q)

-- `size 1 (var 0) ⟶* 1` — the inner call, at the SHIFTED index.
size-var : {Γ : Cx} → size {Γ} (nsuc nzero) (tvar fz) ⟶* nsuc nzero
size-var =
  step (ι-ielim TmD (nsuc nzero) msize zero varPay)
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst msize-var msTail))))
  (step (ξ-appˡ (ξ-appˡ (β (lam (lam (nsuc nzero))) (nsuc nzero))))
  (step (ξ-appˡ (β (lam (nsuc nzero)) varPay))
  (step (β (nsuc nzero) unit) done))))

-- ★★★ `size 0 (λx. x) ⟶* 2`.
size-id : {Γ : Cx} → size {Γ} nzero idTm ⟶* nsuc (nsuc nzero)
size-id =
  step (ι-ielim TmD nzero msize (suc zero) lamPay)
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-fst (βsnd msize-var msTail)))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst msize-lam (pair msize-app unit)))))
  (step (ξ-appˡ (ξ-appˡ (β (lam (lam (nsuc (fst (var vz))))) nzero)))
  (step (ξ-appˡ (β (lam (nsuc (fst (var vz)))) lamPay))
  (step (β (nsuc (fst (var vz)))
           (pair (ielim TmD (nsuc nzero) msize (fst lamPay)) unit))
  -- ★ the IH tuple's first component IS `size (suc 0) …` — the shift.
  (step (ξ-nsuc (βfst (ielim TmD (nsuc nzero) msize (fst lamPay)) unit))
  (step (ξ-nsuc (ξ-ielimᵗ (βfst (tvar fz) unit)))
    (nsucStar size-var))))))))
