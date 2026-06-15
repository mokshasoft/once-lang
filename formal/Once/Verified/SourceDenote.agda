-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceDenote — `⟦_⟧ˢ`, THE source semantics (Plan 0.46 / OCP-0006).
--
-- The single anchor: a typed, FUEL-FREE, total+productive denotational trace
-- semantics directly over the intrinsically-typed surface `Expr` — independent of
-- `elaborate` (so the elaborator stays load-bearing: `⟦ elaborate e ⟧ᴰ ≡ ⟦ e ⟧ˢ`).
--
-- It is a structural fold of `Expr` into the SAME trace monad `T` that `⟦_⟧ᴰ`
-- (the IR view) targets — one meaning, two syntaxes. Totality is Agda's checker
-- (structural recursion on `Expr`); productivity is the `Ana` observation depth.
-- THERE IS NO FUEL: `T`'s `ℕ` is the event-observation depth (D058), consumed
-- only by `Ana`. A fuel parameter here would be a bug (it is how general recursion
-- leaked into the retired `SS.eval`).
--
-- TOP-DOWN (Plan 0.46): the effect/recursion constructors route, for now, to the
-- explicit `⟦⟧ˢ-todo` hole — each is an obligation the apex will demand, not an
-- island. Discharge them as the elaborate-correctness proof (M3) reaches them.
------------------------------------------------------------------------

module Once.Verified.SourceDenote where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ) renaming (∣_∣ to absℤ)
open import Data.List using (List; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)

open import Once.Type
  using (Type; Unit; Void; Int; Str; _*_; _+_; _⇒[_]_; Functor; ⟦_⟧T; μ-type)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ∅)
open import Once.Surface.Elaborate using (⟦_⟧ᶜ)
open import Once.Verified.TraceMonad using (T; returnT; _>>=T_; projTrace; valueT)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ; forget; inject; emit-D)
open import Once.Verified.TraceDenote using (events-F)
open import Once.Verified.Trace using (SigOpEvent)
open import Once.CCC.IR using (IR)
open import Once.CCC.Eval as Val using ()
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine
  using (sem-cata; sem-ana; sem-fmap; coerce-functor; coerce-functor⁻¹; ⟦_⟧F)
open import Once.CCC.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders
  using (add-info; sub-info; mul-info; div-info; mod-info; neg-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info; generic-info; str-lit-info)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- Environment lookup: `⟦Γ⟧ᶜ` is the nested product (`∅ ↦ Unit`,
-- `Γ , A ↦ ⟦Γ⟧ᶜ * A`), so `⟦ ⟦Γ⟧ᶜ ⟧ᴰ` is `… × ⟦A⟧ᴰ`; de-Bruijn `zero`
-- is the most recent binding (`proj₂`), `suc i` recurses into `proj₁`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → ⟦ lookup Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) fzero    dγ = proj₂ dγ
lookupᴰ (Γ , A ^ q) (fsuc i) dγ = lookupᴰ Γ i (proj₁ dγ)

------------------------------------------------------------------------
-- The `Cata` fold's per-layer trace+value algebra, over a ⟦_⟧ˢ algebra
-- CLOSURE (`⟦⟦F⟧T C⟧ᴰ → T ⟦C⟧ᴰ`) rather than an IR — the elaborate-free
-- analogue of `DenotTrace.cata-ev-algᴰ`. Carrier pairs the post-order
-- event trace with the folded (pure) value; children's events precede this
-- layer's algebra events (`projTrace (algClo …)`), value via `forget ∘ valueT`.
------------------------------------------------------------------------

cata-ev-algˢ : ∀ {F C} → ℕ → (⟦ ⟦ F ⟧T C ⟧ᴰ → T ⟦ C ⟧ᴰ)
             → ⟦ F ⟧F (List SigOpEvent × Val.⟦ C ⟧) → List SigOpEvent × Val.⟦ C ⟧
cata-ev-algˢ {F} {C} n algClo fc =
  ( events-F F proj₁ fc ++ projTrace (algClo (inject z)) n
  , forget (valueT (algClo (inject z)) n) )
  where z = coerce-functor⁻¹ F C (sem-fmap F proj₂ fc)

------------------------------------------------------------------------
-- The `Ana` depth-bounded unfold TRACE over a ⟦_⟧ˢ coalgebra CLOSURE — the
-- elaborate-free analogue of `DenotTrace.ana-events`. At depth `suc m`: emit the
-- coalgebra step's events then recurse at `m` on the functor's recursive
-- positions (`events-F`). Structural on `m` (Agda certifies termination of the
-- TRACE prefix; the produced codata is productive — `sem-ana` for the value).
------------------------------------------------------------------------

ana-eventsˢ : ∀ {F A} → (⟦ A ⟧ᴰ → T ⟦ ⟦ F ⟧T A ⟧ᴰ) → Val.⟦ A ⟧ → ℕ → List SigOpEvent
ana-eventsˢ coalgClo a zero    = []
ana-eventsˢ {F} {A} coalgClo a (suc m) =
  projTrace (coalgClo (inject a)) m
    ++ events-F F (λ seed → ana-eventsˢ {F} {A} coalgClo seed m) layer
  where layer = coerce-functor F A (forget (valueT (coalgClo (inject a)) m))

------------------------------------------------------------------------
-- THE SOURCE SEMANTICS. Structural on `Expr`; arrows are Kleisli arrows
-- into `T`; `apply`/`let`/`case` thread the trace via `_>>=T_`.
------------------------------------------------------------------------

⟦_⟧ˢ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A}
     → Expr Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ → T ⟦ A ⟧ᴰ
⟦ var {Γ = Γ} i ⟧ˢ dγ = returnT (lookupᴰ Γ i dγ)
⟦ lam q _ e ⟧ˢ    dγ = returnT (λ a → ⟦ e ⟧ˢ (dγ , a))
⟦ app f x ⟧ˢ      dγ = ⟦ f ⟧ˢ dγ >>=T λ vf → ⟦ x ⟧ˢ dγ >>=T λ vx → vf vx
⟦ pair a b ⟧ˢ     dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (va , vb)
⟦ fst' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (proj₁ v)
⟦ snd' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (proj₂ v)
⟦ inl' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (inj₁ v)
⟦ inr' e ⟧ˢ       dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (inj₂ v)
⟦ case' s l r ⟧ˢ  dγ = ⟦ s ⟧ˢ dγ >>=T λ v →
                         [ (λ a → ⟦ l ⟧ˢ (dγ , a)) , (λ b → ⟦ r ⟧ˢ (dγ , b)) ]′ v
⟦ unit ⟧ˢ         dγ = returnT tt
⟦ absurd e ⟧ˢ     dγ = ⟦ e ⟧ˢ dγ >>=T λ v → ⊥-elim v
⟦ let' e1 e2 ⟧ˢ   dγ = ⟦ e1 ⟧ˢ dγ >>=T λ v1 → ⟦ e2 ⟧ˢ (dγ , v1)
⟦ int n ⟧ˢ        dγ = returnT (absℤ n)
-- str: `str-lit-semM` is ABSTRACT (postulated, unlike the computing lit-int-semM),
-- so the literal's value can't be the clean `s`; denote via its own SigOp `semM`
-- (= `strLit`'s evalᴰ), matching the IR by construction (like arith).
⟦ str s ⟧ˢ        dγ = returnT (semM (str-lit-info s) tt)
-- Arith / comparison / div-mod: all elaborate to `SigOp <op>-info` (Pure), so
-- denote them through the SAME `semM` — `⟦ op a b ⟧ˢ` is then DEFINITIONALLY the
-- IR side `⟦ <op>IR ∘ ⟨a,b⟩ ⟧ᴰ`, making M3's elaborate-correctness trivial here.
⟦ add a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM add-info (va , vb))
⟦ sub a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM sub-info (va , vb))
⟦ mul a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM mul-info (va , vb))
⟦ div a b ⟧ˢ      dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM div-info (va , vb))
⟦ mod' a b ⟧ˢ     dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM mod-info (va , vb))
⟦ neg e ⟧ˢ        dγ = ⟦ e ⟧ˢ dγ >>=T λ v → returnT (semM neg-info v)
⟦ lt a b ⟧ˢ       dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM lt-info (va , vb))
⟦ le a b ⟧ˢ       dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM le-info (va , vb))
⟦ gt a b ⟧ˢ       dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM gt-info (va , vb))
⟦ ge a b ⟧ˢ       dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM ge-info (va , vb))
⟦ eq a b ⟧ˢ       dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM eq-info (va , vb))
⟦ ne a b ⟧ˢ       dγ = ⟦ a ⟧ˢ dγ >>=T λ va → ⟦ b ⟧ˢ dγ >>=T λ vb → returnT (semM ne-info (va , vb))
⟦ arr' f ⟧ˢ       dγ = ⟦ f ⟧ˢ dγ
-- effApp: a SUSPENDED effect (`Unit ⇒[eff] B`) — the Eff design (D018). The
-- effectful application is deferred into the Unit-thunk; its trace fires when the
-- thunk is applied (at the top-level main run), threaded by `T`. No fork: the old
-- immediate-vs-suspended mismatch was SS.eval (retired) vs the IR; one semantics
-- now, and the Eff type IS suspended.
⟦ effApp f x ⟧ˢ   dγ = returnT (λ _ → ⟦ f ⟧ˢ dγ >>=T λ vf → ⟦ x ⟧ˢ dγ >>=T λ vx → vf vx)
-- IR embedding: `lift-morphism`/`morph-app` inject a PRE-BUILT CCC morphism into
-- the surface; their meaning IS the IR's denotation `evalᴰ ir` (definitionally
-- matching elaborate, which maps them straight to `ir`). Not the IR-pivot — these
-- are leaves embedding a fixed morphism, not the elaboration of a user subterm.
⟦ lift-morphism ir ⟧ˢ dγ = returnT (evalᴰ ir)
⟦ morph-app ir e ⟧ˢ   dγ = ⟦ e ⟧ˢ dγ >>=T λ v → evalᴰ ir v
-- Cata: the structural fold. The algebra is CLOSED (∅), so `⟦alg⟧ˢ tt` is the
-- algebra closure; fold via `sem-cata` over `cata-ev-algˢ` (trace+value carrier),
-- mirroring `evalᴰ (Cata …)` but elaborate-free (uses `⟦alg⟧ˢ`, not `evalᴰ alg`).
⟦ cata {F = F} {A = A} wf alg ⟧ˢ dγ =
  returnT (λ x → λ n →
    let r = sem-cata wf (cata-ev-algˢ {F} {A} n (valueT (⟦ alg ⟧ˢ tt) 0)) x
    in (proj₁ r , inject (proj₂ r)))
-- Ana: the productive unfold. Coalgebra CLOSED (∅) → `⟦coalg⟧ˢ tt` is the
-- closure. TRACE via `ana-eventsˢ` (depth-bounded prefix, the SOLE T-ℕ consumer);
-- VALUE via `sem-ana` (the codata), mirroring `eval (Ana …)` but elaborate-free.
⟦ ana {F = F} {A = A} wf coalg ⟧ˢ dγ =
  returnT (λ a → λ n →
    ( ana-eventsˢ {F} {A} (valueT (⟦ coalg ⟧ˢ tt) 0) (forget a) n
    , inject (sem-ana F (λ a' → coerce-functor F _
                  (forget (valueT (valueT (⟦ coalg ⟧ˢ tt) 0 (inject a')) 0))) (forget a)) ))
-- Effect primitives (sigOp/closure/poly): named external ops resolved to
-- `generic-info name`, emitting + valued via the SAME emit-D/semM the IR uses
-- (definitionally = elaborate's `SigOp (generic-info name) ∘ terminal`). sigOp
-- DISPATCHES ON RESULT-TYPE SHAPE (matching elaborate): at an arrow it is a
-- CLOSURE applying the SigOp to its arg (so the effect fires at apply, not at
-- pair-build); at non-arrow it runs on terminal `tt`. closure/poly never wrap.
⟦ sigOp {A = (Dom ⇒[ k ] Cod)} name ⟧ˢ dγ =
  returnT (λ arg → λ n → ( emit-D (generic-info {Dom} {Cod} name) (forget arg)
                         , inject (semM (generic-info {Dom} {Cod} name) (forget arg)) ))
⟦ sigOp {A = A} name ⟧ˢ   dγ = λ n → (emit-D (generic-info {Unit} {A} name) tt , inject (semM (generic-info {Unit} {A} name) tt))
⟦ closure {A = A} name ⟧ˢ dγ = λ n → (emit-D (generic-info {Unit} {A} name) tt , inject (semM (generic-info {Unit} {A} name) tt))
⟦ poly name PT ⟧ˢ         dγ = λ n → (emit-D (generic-info {Unit} {PT} name) tt , inject (semM (generic-info {Unit} {PT} name) tt))
