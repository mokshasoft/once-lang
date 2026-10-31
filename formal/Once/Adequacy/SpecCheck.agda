-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCheck — `once check` decides the Spec's typing of a
-- module (plan 0.133, D355).
--
-- `once check` reads a source the way `once build` does — the module texts
-- parsed (`toSource`), the program's text parsed and its imports resolved
-- (`srcToModule`) — and asks `check` (`Once.Inspect`). It accepts exactly the
-- sources the Spec types as a module (`Spec.Source._⊢ᴹ_`): a library over its
-- signature, every definition named `main` an entry. A program is such a
-- module with an entry (`_⊢_`); a module without one is a library, and
-- `check` accepts it too.
--
-- Soundness is `DenoteModule.denoteᴹ` (the library the compiler's telescope
-- denotes); completeness is `TypedBack.checked←` (the compiler types what the
-- Spec does). Neither depends on a target: a library is not run.
------------------------------------------------------------------------

module Once.Adequacy.SpecCheck where

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Source using (Source; TypedModule; _⊢ᴹ_)
import Once.Spec.Source as SP
import Once.Spec.Surface.Syntax as SS
import Once.Denotation.Behavior as B
import Once.Parser as Parser
import Once.Parser.Module.Core as PM
open import Once.Parser.Module.Resolve using (collectUnaliased; collectAliases; importedOf)
import Once.Parser.Relation.Parsing as LPa
import Once.Parser.Relation.Resolution as LR
open import Once.Adequacy.SpecSource using (parseModules; toSource)
open import Once.Adequacy.SourceTrace using (srcToModule; srcToModule-just; srcToModule-inv)
import Once.Adequacy.FrontEndBridge as FB
import Once.Adequacy.ResolveBridge as RBR
open import Once.Inspect using (check)
open import Once.Inspect.Proof using (CheckedEF; Checked; check-decides)
import Once.Adequacy.SpecGrammar.Decl as GD
import Once.Adequacy.SpecGrammar.Written as Written
import Once.Adequacy.SpecFront.Modules as Modules
import Once.Adequacy.SpecFront.Words as Words
import Once.Adequacy.SpecFront.DenoteModule as DM
import Once.Adequacy.SpecFront.TypedBack as TB

------------------------------------------------------------------------
-- What `once check` does with a Spec source
------------------------------------------------------------------------

-- The texts parse, the module resolves, and `check` accepts it.
Checks : Source → Set
Checks src = Σ[ srcC ∈ B.Source ] (toSource src ≡ just srcC)
           × Σ[ m ∈ PM.Resolved ] (srcToModule srcC ≡ just m) × (check m ≡ inj₂ tt)

------------------------------------------------------------------------
-- Soundness: what `check` accepts, the Spec types
------------------------------------------------------------------------

private
  bind-just : ∀ {A C : Set} (m : Maybe A) (f : A → Maybe C) {c}
            → (m >>= f) ≡ just c → Σ[ a ∈ A ] (m ≡ just a) × (f a ≡ just c)
  bind-just (just a) f eq = a , refl , eq

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  -- over the extractor's result, so the compiler's typing reduces
  sound-ef : ∀ (src : Source) {mm dsU dsR}
           → parseModules (SP.Source.modules src) ≡ just mm
           → LPa.ParsesText (SP.Source.text src) (SS.mkModule dsU)
           → LR.ResolvesDecls mm (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR
           → (ef : String ⊎ List Parser.Entry) → Parser.extractFunctions (PM.resolved (SS.mkModule dsR) (importedOf mm dsU)) ≡ ef
           → CheckedEF ef → Σ[ tm ∈ TypedModule ] src ⊢ᴹ tm
  sound-ef src pm pt rds (inj₁ _) eq ()
  sound-ef src {mm} {dsU} pm pt rds (inj₂ es) eq (mt , ms) =
    record { module′ = SS.mkModule dsU ; signature = DM.ModuleDenoted.Σₛ D
           ; library = record { wf = DM.ModuleDenoted.wf D ; defs = DM.ModuleDenoted.tele D } }
    , mm , pt′ , pms , DM.ModuleDenoted.denotes D
    where
      pms = Modules.modules-of (SP.Source.modules src) pm
      pt′ = GD.parses→ {SP.Source.text src} pt
      D = DM.denoteᴹ (Words.mods-words pms) (Words.decls-words {SP.Source.text src} pt′) rds eq mt ms

check-sound : ∀ (src : Source) → Checks src → Σ[ tm ∈ TypedModule ] src ⊢ᴹ tm
check-sound src (srcC , ts , m , stm , ok) =
  let (mm , pm , e) = bind-just (parseModules (SP.Source.modules src)) _ ts
  in at (just-inj e) pm stm ok
  where
    at : ∀ {mm} → B.mkSource mm (SP.Source.text src) ≡ srcC → parseModules (SP.Source.modules src) ≡ just mm
       → srcToModule srcC ≡ just m → check m ≡ inj₂ tt → Σ[ tm ∈ TypedModule ] src ⊢ᴹ tm
    at {mm} refl pm stm ok with srcToModule-inv (B.mkSource mm (SP.Source.text src)) m stm
    ... | mU , p-eq , r-eq with RBR.resolvesModule-complete mm (SS.Module.decls mU) m r-eq
    ...   | LR.rm {ds' = dsR} rds =
            sound-ef src pm (FB.parseStrict-sound (SP.Source.text src) mU p-eq) rds _ refl
                     (Equivalence.to (check-decides (PM.resolved (SS.mkModule dsR) (importedOf mm (SS.Module.decls mU)))) ok)

------------------------------------------------------------------------
-- Completeness: what the Spec types, `check` accepts
------------------------------------------------------------------------

check-complete : ∀ (src : Source) → Σ[ tm ∈ TypedModule ] src ⊢ᴹ tm → Checks src
check-complete src (tm , mm , pt′ , pms , den) =
  B.mkSource mm (SP.Source.text src) , Modules.source-of← src pms
  , m , stm , Equivalence.from (check-decides m) (TB.CheckedC.checked T)
  where
    mU = TypedModule.module′ tm
    dsU = SS.Module.decls mU
    T = TB.checked← (Words.mods-words pms) (Words.decls-words {SP.Source.text src} pt′)
                    (Written.decls-written {SP.Source.text src} pt′) den
    m = PM.resolved (SS.mkModule (TB.CheckedC.dsR T)) (importedOf mm dsU)
    stm : srcToModule (B.mkSource mm (SP.Source.text src)) ≡ just m
    stm = srcToModule-just (B.mkSource mm (SP.Source.text src)) mU m
            (FB.parseStrict-complete (SP.Source.text src) mU (GD.parses← {SP.Source.text src} pt′))
            (RBR.resolvesModule-sound mm dsU m (LR.rm (TB.CheckedC.rds T)))

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

-- `once check` accepts a source exactly when the Spec types it as a module.
check-is-typing : ∀ (src : Source) → Checks src ⇔ (Σ[ tm ∈ TypedModule ] src ⊢ᴹ tm)
check-is-typing src = mk⇔ (check-sound src) (check-complete src)

-- What the apex says of `once check` (`CertifiedBuild.checker`).
record VerifiedChecker : Set₁ where
  field
    is-typing : ∀ (src : Source) → Checks src ⇔ (Σ[ tm ∈ TypedModule ] src ⊢ᴹ tm)

verifiedChecker : VerifiedChecker
verifiedChecker = record { is-typing = check-is-typing }
