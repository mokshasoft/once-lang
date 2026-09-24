------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `cong!`: THE CONGRUENCE POSITION, FOUND FOR YOU.
--
-- ⚠ THE PROBLEM IT SOLVES.  `RedCong` has 138 congruences, and a proof
--   author must NAME the one matching the position they want to reduce
--   at.  Measured: the evaluator work cut tokens/row 98 → 34 (−65%) but
--   left the VOCABULARY at 22 and plumbing:content at 15:1 — writing got
--   shorter, THINKING did not.
--
-- ⚠⚠ AND AGDA CANNOT INFER THE POSITION.  With a one-hole context as a
--   term (`subTm (single t) F`) the use site needs `wk-single` and does
--   not typecheck at all; as a DATATYPE it typechecks but
--       plug _C_131 t = app t u   (blocked on _C_131)
--   — inverting `plug` is higher-order unification.
--
-- ★★★ SO WE WRITE THE UNIFICATION OURSELVES — but NOT as an Agda
--   function.  Every `dec*`-style function sticks on abstract arguments
--   (`decVar vz a != nothing`), which is the same wall that stopped the
--   normaliser and the equation-shaped adequacy.  A MACRO runs at
--   ELABORATION time, where the goal's SYNTAX is concrete even when its
--   TERMS are abstract:
--       probe : {t t' u : RTm Γ} → t ⟶* t' → app t u ⟶* app t' u
--       ⇒ GOAL = app t u ⟶* app t' u
--
-- ★ AND EQUALITY ON `RTm` IS NEVER NEEDED: "identical" is just "the
--   parallel walk found no difference", so the recursion decides it.
--   The abstraction that blocks `decTm` lives in `RTm`; the walk runs on
--   `Term`, an ordinary datatype with concrete constructors.
--
-- ⚠ `--safe` forbids {-# TERMINATING #-}, so the walk is STRUCTURAL:
--   the `Arg` list is passed straight down (a subterm) and visibility is
--   filtered inside, rather than mapped first.
--
-- ⚠ Reflection is ALREADY ESTABLISHED HERE — `Metatheory/FormerCensus`
--   uses a `macro` under `--safe`, and records it was measured
--   2026-09-01.  This is not a new dependency.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.CongMacro where

open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using ( Nat; zero; suc )
open import Agda.Builtin.Maybe
open import Agda.Builtin.Unit using ( ⊤; tt )
-- ⚠ `lam` is AMBIGUOUS with `Reflection.Term.lam`; rename on import so
--   `quote` has an unambiguous name to take.
open import DirectedHoTT.Spec.Syntax
  using ( app; pair; fst; snd; icon; ielim; nsuc; jsub )
  renaming ( lam to Rlam )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-lam; ⟶*-icon; ⟶*-nsuc; ⟶*-jsubᵖ
        ; ⟶*-ielimⁱ; ⟶*-ielimᵐ; ⟶*-ielimᵗ )

ite : {A : Set} → Bool → A → A → A
ite true  x _ = x
ite false _ y = y

eqN : Nat → Nat → Bool
eqN zero    zero    = true
eqN (suc a) (suc b) = eqN a b
eqN _       _       = false

-- ★ THE TABLE: (former , which VISIBLE argument differs) → the
--   congruence that lifts it.  One line per congruence; extending the
--   macro's coverage is adding a row here.
--
-- ⚠ VISIBLE index, not the constructor's arity: `icon k p` has `k : ℕ`
--   at 0 so the payload is 1, and `ielim D i ms t` has the description
--   at 0 so the scrutinee is 3.
data Entry : Set where
  ent : Name → Nat → Name → Entry

table : List Entry
table = ent (quote app)   0 (quote ⟶*-appˡ)
      ∷ ent (quote app)   1 (quote ⟶*-appʳ)
      ∷ ent (quote pair)  0 (quote ⟶*-pairˡ)
      ∷ ent (quote pair)  1 (quote ⟶*-pairʳ)
      ∷ ent (quote fst)   0 (quote ⟶*-fst)
      ∷ ent (quote snd)   0 (quote ⟶*-snd)
      ∷ ent (quote Rlam)  0 (quote ⟶*-lam)
      ∷ ent (quote nsuc)  0 (quote ⟶*-nsuc)
      ∷ ent (quote icon)  1 (quote ⟶*-icon)
      ∷ ent (quote jsub)  1 (quote ⟶*-jsubᵖ)
      ∷ ent (quote ielim) 1 (quote ⟶*-ielimⁱ)
      ∷ ent (quote ielim) 2 (quote ⟶*-ielimᵐ)
      ∷ ent (quote ielim) 3 (quote ⟶*-ielimᵗ)
      ∷ []

congFor : Name → Nat → Maybe Name
congFor c i = look table
  where
    look : List Entry → Maybe Name
    look []               = nothing
    look (ent n j r ∷ es) =
      ite (primQNameEquality c n) (ite (eqN i j) (just r) (look es)) (look es)

path  : Term → Term → Maybe (List Name)
paths : Name → Nat → List (Arg Term) → List (Arg Term) → Maybe (List Name)

path (con c as) (con d bs) = ite (primQNameEquality c d) (paths c 0 as bs) (just [])
path _ _ = just []                     -- differ, or opaque ⇒ the hole is HERE

paths c i (arg (arg-info visible _) x ∷ xs) (arg (arg-info visible _) y ∷ ys)
  with path x y
... | nothing = paths c (suc i) xs ys                    -- identical, keep going
... | just p  with congFor c i
...              | just nm = just (nm ∷ p)
...              | nothing = just []
paths c i (_ ∷ xs) (_ ∷ ys) = paths c i xs ys            -- skip implicits
paths _ _ []       []       = nothing                    -- identical
paths _ _ _        _        = just []

varg : Term → Arg Term
varg = arg (arg-info visible (modality relevant quantity-ω))

build : List Name → Term → Term
build []       p = p
build (n ∷ ns) p = def n (varg (build ns p) ∷ [])

sides : List (Arg Term) → Maybe (List Name)
sides (arg (arg-info visible _) l ∷ arg (arg-info visible _) r ∷ []) = path l r
sides (_ ∷ as) = sides as
sides []       = nothing

macro
  cong! : Term → Term → TC ⊤
  cong! p hole =
    bindTC (inferType hole) λ g → go g
    where
      go : Term → TC ⊤
      go (def _ as) with sides as
      ... | just ns = unify hole (build ns p)
      ... | nothing = typeError (strErr "cong!: the goal's two sides are identical" ∷ [])
      go t = typeError (strErr "cong!: goal is not a reduction: " ∷ termErr t ∷ [])
