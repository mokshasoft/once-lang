-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.NoCopyCore — plan 0.157 S2 step 3 (D6, D500): ★ THE BRIDGE
-- HALF OF `NoCopy`, for a whole program.
--
-- A program `once check` gives no "not linear" warning (`ExprImage.linearSites`
-- empty) has a core table and a `main` that name no copy of cells
-- (`CopyFree.CF`, at the program's lent-called types): each definition's body
-- by `LinearCF.linear-cf`, the rest of a body (its erasure, its direct-call
-- shape) and `main` (a call) by construction. The machine half — no run of the
-- emitted image enters a copy block — is step 4 (`Implementation.NoCopy`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.NoCopyCore (fmt : TargetNum) where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Once.Spec.Grade as G
open import Once.Spec.Type using (Type; _⇒[_]_)
import Once.Spec.Type as ST
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-unit; sub-void)
open import Once.Spec.Name using (bare)
open import Once.Compile using (EffUU)
open import Once.IRTy using (⌊_⌋)
import Once.IRTy
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc; Src; src; module Src)

open import Once.LinCore.Core fmt
open import Once.LinCore.FromIR fmt using (⟪_⟫; grade)
open import Once.LinCore.FromExpr fmt using (Rs; ty)
open import Once.LinCore.ExprBuild fmt using (eraseL; dc; val; bodyOf; exprTable; ETProg; module ETProg; mainCore; srcOrder)
open import Once.LinCore.Linear fmt using (sites)
open import Once.LinCore.CopyFree fmt using (CF; CFD)
open import Once.LinCore.LinearCF fmt using (linear-cf; cf-cast; cf-callM; ++-[])
open import Once.LinCore.Loader using (bw)
import Once.LinCore.Keys
import Once.LinCore.ExprImage

module _ (lc : LTy → Bool) where

  -- a definition the checker passes (no warning)
  LinearSrc : CompiledSrc → Set
  LinearSrc c = sites lc (Src.expr (CompiledSrc.csSrc c)) ≡ []

  cf-eraseL : ∀ {L E m n} (Γ : Ctx m n) (Ψ : Usage n) → CF lc (eraseL {L} {E} Γ Ψ)
  cf-eraseL SC.∅          []           = tt
  cf-eraseL (Γ SC.▸ A) (G.Zero ∷ Ψ) = cf-eraseL Γ Ψ , _
  cf-eraseL (Γ SC.▸ A) (G.One  ∷ Ψ) = cf-eraseL Γ Ψ , tt
  cf-eraseL (Γ SC.▸ A) (G.Many ∷ Ψ) = cf-eraseL Γ Ψ , tt

  cf-dc : ∀ {L} (T : Type) {v : LTm L One (ty T)} → CF lc v → CF lc (dc {L} T v)
  cf-dc (A ⇒[ G.mk-kind G.Zero π ] B) c = tt , ((c , tt) , tt)
  cf-dc (A ⇒[ G.mk-kind G.One π ] B)  c = tt , ((c , tt) , tt)
  cf-dc (A ⇒[ G.mk-kind G.Many π ] B) c = tt , ((c , tt) , tt)
  cf-dc ST.Unit      c = c
  cf-dc ST.Void      c = c
  cf-dc (X ST.* Y)   c = c
  cf-dc (X ST.+ Y)   c = c
  cf-dc (ST.μ F)     c = c
  cf-dc (ST.ν F f)   c = c
  cf-dc ST.Int       c = c
  cf-dc ST.Float     c = c
  cf-dc (ST.var ())  c

  cf-val : ∀ {L T} (rs : Rs L) (s : Src T) → sites lc (Src.expr s) ≡ [] → CF lc (val rs s)
  cf-val {L} rs (src {Γ = Γ} {Ψ = Ψ} δ₀ m opt e) h =
    cf-cast lc {L} (cong ⟪_⟫ (cong ⌊_⌋ δ₀)) refl (linear-cf lc rs e h , cf-eraseL Γ Ψ)

  -- ★ the table of a program whose definitions the checker passes
  cf-table : ∀ (tl : List CompiledSrc) → All LinearSrc tl → CFD lc (ETProg.defs (exprTable tl))
  cf-table []       []       = tt
  cf-table (c ∷ cs) (h ∷ hs) =
    cf-table cs hs , (cf-dc (CompiledSrc.csType c) (cf-val (ETProg.rs (exprTable cs)) (CompiledSrc.csSrc c) h) , tt)

  -- `main`: a call
  cf-main : ∀ {L} (rs : Rs L) {T : Type} (pm : T <: EffUU) → CF lc (mainCore rs pm)
  cf-main rs (sub-arr {π = π} a sub-unit g) = cf-callM lc (rs (bare "main") Once.IRTy.Unit Once.IRTy.Unit (grade π))
  cf-main rs (sub-arr {π = π} a sub-void g) = tt , cf-callM lc (rs (bare "main") Once.IRTy.Unit Once.IRTy.Void (grade π))
  cf-main rs sub-void                      = tt , cf-callM lc (rs (bare "main") Once.IRTy.Unit Once.IRTy.Void act)

------------------------------------------------------------------------
-- ★ No warning ⇒ the program's core copies nothing.
------------------------------------------------------------------------

private
  concatMap-[] : ∀ {X Y : Set} (f : X → List Y) (xs : List X) → concatMap f xs ≡ [] → All (λ x → f x ≡ []) xs
  concatMap-[] f []       _ = []
  concatMap-[] f (x ∷ xs) e = proj₁ (++-[] (f x) e) ∷ concatMap-[] f xs (proj₂ (++-[] (f x) e))

  map-[] : ∀ {X Y : Set} (f : X → Y) (xs : List X) → map f xs ≡ [] → xs ≡ []
  map-[] f []      _ = refl
  map-[] f (_ ∷ _) ()

-- the program's lent-called closure types (D498), as the warning reads them
lcOf : (tl : List CompiledSrc) → ∀ {T : Type} → T <: EffUU → LTy → Bool
lcOf tl pm = Once.LinCore.Keys.Univ.lct (Once.LinCore.Keys.univ fmt bw (ETProg.defs (exprTable tl)) (mainCore (ETProg.rs (exprTable tl)) pm))

no-copy-core : ∀ (tl : List CompiledSrc) {T : Type} (pm : T <: EffUU)
             → Once.LinCore.ExprImage.linearSites fmt tl pm ≡ []
             → CFD (lcOf tl pm) (ETProg.defs (exprTable tl)) × CF (lcOf tl pm) (mainCore (ETProg.rs (exprTable tl)) pm)
no-copy-core tl pm h =
  cf-table (lcOf tl pm) tl
    (Data.List.Relation.Unary.All.map (λ {c} e → map-[] _ (sites (lcOf tl pm) (Src.expr (CompiledSrc.csSrc c))) e) (concatMap-[] _ tl h))
  , cf-main (lcOf tl pm) (ETProg.rs (exprTable tl)) pm
