------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 7 — DYNAMIC allocation cost.
--
-- linearization-6 closed the exponential gap but surfaced a problem with the
-- payoff theorem: `dupCount` is a STATIC count of `dup` GENERATORS, and once
-- closures exist it is not the number of allocations a run performs. This
-- module replaces the count with an instrumented COST SEMANTICS and settles
-- exactly how the two relate.
--
--   * `⟦_⟧C`  — the instrumented value domain. Identical to the evaluator's
--               `⟦_⟧T` EXCEPT at `⇒`, where a function reports its own cost:
--               `⟦ A ⇒ B ⟧C = ⟦ A ⟧C → ⟦ B ⟧C × ℕ`. (`μ F` is unchanged —
--               `Func` is `Ty`-independent, so `Fix F` holds no functions.)
--   * `Lᶜ`    — the cost semantics: `LTm A B → ⟦ A ⟧C → ⟦ B ⟧C × ℕ`, the
--               writer-monad reading of `NbEPLinPass.Lⁱ`. `dup` is the only
--               generator with nonzero cost; building a closure is FREE and
--               its body's cost is paid at `leval`, once per application.
--   * `Free`  — a LOGICAL RELATION "this value allocates nothing when used",
--               needed because `DupFree` alone cannot bound `leval`: its input
--               closure is an arbitrary semantic value.
--   * `dyn-linear` — ★ THE OPERATIONAL LINEARITY THEOREM: a `DupFree` morphism,
--               applied to `Free` inputs, performs ZERO allocations at RUNTIME
--               and returns a `Free` result. This upgrades
--               `NbEPLinPass.dupfree-no-alloc` from a syntactic identity to a
--               statement about execution — "the linear sublanguage allocates
--               nothing" as a theorem about runs, not about syntax.
--
-- ★ THE FOUR DIVERGENCES, all witnessed by `refl` below. The finding is
-- stronger than linearization-6 recorded: `dupCount` is neither an upper nor a
-- lower bound in general, and CLOSURES ARE NOT THE ONLY CAUSE — `case` already
-- breaks it in the first-order fragment:
--
--   (a) `case`    — static OVERCOUNTS. `dupCount (lcase f g)` adds BOTH
--                   branches; a run takes one. (`case-over`.)
--   (b) `lcurry`  — static OVERCOUNTS AT BUILD TIME: making a closure costs
--                   nothing, whatever its body contains (`closure-build-free`)…
--   (c) `lcurry`  — …and UNDERCOUNTS OVER A RUN: the body's dups fire once per
--                   APPLICATION, so `n` applications cost `n ×` the static
--                   figure (`closure-per-app`, `closure-twice`).
--   (d) `lcata`   — static UNDERCOUNTS: the algebra runs once per NODE
--                   (`cata-under`: a 3-node tree pays 2 for a static 1).
--
-- ⇒ `NbEPLinPass.pass-alloc` remains exactly true AS A SYNTACTIC IDENTITY, and
-- is the right statement for comparing pass output against pass input. It is
-- NOT an operational allocation bound. The operational content is `dyn-linear`
-- (zero for the linear fragment) plus, for the non-linear fragment, a figure
-- that depends on the RUN — branch taken, tree size, application count — and
-- therefore cannot be read off the syntax at all.
--
-- HONEST SCOPE. Agreement between `Lᶜ`'s value component and `Lⁱ` is not
-- proven here: they live in different domains (`⟦_⟧C` vs `⟦_⟧T`), so relating
-- them needs a section/retraction pair at `⇒` and funext — a logical relation
-- of its own. `Lᶜ` is offered as the SPECIFICATION of dynamic cost; its value
-- component is `Lⁱ`'s definition verbatim modulo the writer.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinDyn where

open import normalizer.Syntax.Types
  using ( Ty; Void; Unit; _*_; _+_; _⇒_; μ_; ⟦_⟧F
        ; Func; Id; One; Kc; _⊕_; _⊗_
        ; ⊥; ⊤; tt; _×_; _,_; Σ; _⊎_; inj₁; inj₂
        ; _≡_; refl; cong; cong₂ )
open Σ using ( fst; snd )
open import normalizer.Syntax.CCC using ( Term )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧FS; Fix; fix; cata-Set; map-cata-Set )
open import poc.OCP0009.NbEPLinRec
  using ( LTm; lid; _∘l_; _⊗l_; ρl; ρl⁻; lul; lul⁻; dup; drop
        ; linl; linr; lcase; lIn; lcata; lcurry; leval
        ; fstL; sndL; ⟨_,_⟩L; lassoc; lassoc⁻; lswap
        ; DupFree; df-∘; df-⊗; df-id; df-ρl; df-ρl⁻; df-lul; df-lul⁻
        ; df-drop; df-linl; df-linr; df-case; df-In; df-cata
        ; df-lcurry; df-leval; df-lassoc; df-lassoc⁻; df-lswap )
open import poc.OCP0009.NbEPLinPass
  using ( ℕ; zero; suc; _+ℕ_; dupCount; FO; PairFree; pass-df; L⟦_⟧ )

------------------------------------------------------------------------
-- The instrumented value domain and the cost (writer) monad.
------------------------------------------------------------------------

⟦_⟧C : Ty → Set
⟦ Void ⟧C  = ⊥
⟦ Unit ⟧C  = ⊤
⟦ A * B ⟧C = ⟦ A ⟧C × ⟦ B ⟧C
⟦ A + B ⟧C = ⟦ A ⟧C ⊎ ⟦ B ⟧C
⟦ A ⇒ B ⟧C = ⟦ A ⟧C → ⟦ B ⟧C × ℕ   -- ★ a function reports its own cost
⟦ μ F ⟧C   = Fix F

retᶜ : ∀ {X : Set} → X → X × ℕ
retᶜ x = (x , zero)

infixl 1 _>>=ᶜ_
_>>=ᶜ_ : ∀ {X Y : Set} → X × ℕ → (X → Y × ℕ) → Y × ℕ
(x , m) >>=ᶜ k = (fst (k x) , (m +ℕ snd (k x)))

------------------------------------------------------------------------
-- The functor coherence, at the instrumented domain (same five cases as the
-- evaluator's `coherence`; `⟦_⟧F` only reshapes, so nothing changes).
------------------------------------------------------------------------

cohC : ∀ F A → ⟦ ⟦ F ⟧F A ⟧C → ⟦ F ⟧FS ⟦ A ⟧C
cohC Id      A x        = x
cohC One     A x        = x
cohC (Kc G)  A x        = x
cohC (F ⊕ G) A (inj₁ x) = inj₁ (cohC F A x)
cohC (F ⊕ G) A (inj₂ y) = inj₂ (cohC G A y)
cohC (F ⊗ G) A (x , y)  = (cohC F A x , cohC G A y)

cohC⁻¹ : ∀ F A → ⟦ F ⟧FS ⟦ A ⟧C → ⟦ ⟦ F ⟧F A ⟧C
cohC⁻¹ Id      A x        = x
cohC⁻¹ One     A x        = x
cohC⁻¹ (Kc G)  A x        = x
cohC⁻¹ (F ⊕ G) A (inj₁ x) = inj₁ (cohC⁻¹ F A x)
cohC⁻¹ (F ⊕ G) A (inj₂ y) = inj₂ (cohC⁻¹ G A y)
cohC⁻¹ (F ⊗ G) A (x , y)  = (cohC⁻¹ F A x , cohC⁻¹ G A y)

------------------------------------------------------------------------
-- Folding with a cost-carrying algebra: the children's costs are summed out
-- of the functor, then the algebra's own cost is added. This is where "once
-- per node" becomes visible.
------------------------------------------------------------------------

sumF : ∀ G {X : Set} → ⟦ G ⟧FS (X × ℕ) → ⟦ G ⟧FS X × ℕ
sumF Id      p        = p
sumF One     t        = retᶜ t
sumF (Kc G)  t        = retᶜ t
sumF (G ⊕ H) (inj₁ y) = (inj₁ (fst (sumF G y)) , snd (sumF G y))
sumF (G ⊕ H) (inj₂ z) = (inj₂ (fst (sumF H z)) , snd (sumF H z))
sumF (G ⊗ H) (y , z)  =
  ((fst (sumF G y) , fst (sumF H z)) , (snd (sumF G y) +ℕ snd (sumF H z)))

cataStep : ∀ F {X : Set} → (⟦ F ⟧FS X → X × ℕ) → ⟦ F ⟧FS (X × ℕ) → X × ℕ
cataStep F alg w = sumF F w >>=ᶜ alg

cataC : ∀ F {X : Set} → (⟦ F ⟧FS X → X × ℕ) → Fix F → X × ℕ
cataC F alg = cata-Set F (cataStep F alg)

------------------------------------------------------------------------
-- ★ THE COST SEMANTICS.
------------------------------------------------------------------------

Lᶜ : ∀ {A B} → LTm A B → ⟦ A ⟧C → ⟦ B ⟧C × ℕ
Lᶜ lid           x        = retᶜ x
Lᶜ (f ∘l g)      x        = Lᶜ g x >>=ᶜ Lᶜ f
Lᶜ (f ⊗l g)      (a , b)  = Lᶜ f a >>=ᶜ λ a' → Lᶜ g b >>=ᶜ λ b' → retᶜ (a' , b')
Lᶜ ρl            (a , tt) = retᶜ a
Lᶜ ρl⁻           a        = retᶜ (a , tt)
Lᶜ lul           (tt , a) = retᶜ a
Lᶜ lul⁻          a        = retᶜ (tt , a)
-- ★ the structural isos are FREE: reassociating and braiding move data, they
-- do not copy it. This is what makes a graded context split cost nothing.
Lᶜ lassoc        ((a , b) , c) = retᶜ (a , (b , c))
Lᶜ lassoc⁻       (a , (b , c)) = retᶜ ((a , b) , c)
Lᶜ lswap         (a , b)  = retᶜ (b , a)
Lᶜ dup           a        = ((a , a) , (suc zero))  -- ★ THE allocation
Lᶜ drop          a        = retᶜ tt
Lᶜ linl          a        = retᶜ (inj₁ a)
Lᶜ linr          b        = retᶜ (inj₂ b)
Lᶜ (lcase f g)   (inj₁ a) = Lᶜ f a                 -- ★ only the taken branch
Lᶜ (lcase f g)   (inj₂ b) = Lᶜ g b
Lᶜ (lIn {F})     x        = retᶜ (fix (cohC F (μ F) x))
Lᶜ (lcata F alg) x        = cataC F (λ y → Lᶜ alg (cohC⁻¹ F _ y)) x  -- ★ per node
Lᶜ (lcurry f)    a        = retᶜ (λ b → Lᶜ f (a , b))  -- ★ building is FREE…
Lᶜ leval         (f , a)  = f a                        -- ★ …paid HERE, per call

------------------------------------------------------------------------
-- ★ DIVERGENCE (a) — `case`: the static count adds both branches, a run pays
-- for one. Take a term whose left branch dups and whose right branch does not.
------------------------------------------------------------------------

caseT : ∀ {A} → LTm (A + A) A
caseT = lcase (fstL ∘l dup) lid

case-static : ∀ {A} → dupCount (caseT {A}) ≡ suc zero
case-static = refl

-- …but running the RIGHT branch allocates nothing.
case-over : ∀ {A} (a : ⟦ A ⟧C) → snd (Lᶜ (caseT {A}) (inj₂ a)) ≡ zero
case-over a = refl

-- (and the left branch does pay its one allocation)
case-left : ∀ {A} (a : ⟦ A ⟧C) → snd (Lᶜ (caseT {A}) (inj₁ a)) ≡ suc zero
case-left a = refl

------------------------------------------------------------------------
-- ★ DIVERGENCES (b)/(c) — closures: free to build, charged per application.
------------------------------------------------------------------------

-- a closure whose BODY duplicates: `λ b → (fst ∘ dup ∘ fst) (a , b)`.
closT : ∀ {A B} → LTm A (B ⇒ A)
closT = lcurry (fstL ∘l dup ∘l fstL)

clos-static : ∀ {A B} → dupCount (closT {A} {B}) ≡ suc zero
clos-static = refl

-- (b) building it is FREE, though the static count says 1.
closure-build-free : ∀ {A B} (a : ⟦ A ⟧C) → snd (Lᶜ (closT {A} {B}) a) ≡ zero
closure-build-free a = refl

-- (c) each APPLICATION pays the body's allocation.
closure-per-app : ∀ {A B} (a : ⟦ A ⟧C) (b : ⟦ B ⟧C) →
                  snd (fst (Lᶜ (closT {A} {B}) a) b) ≡ suc zero
closure-per-app a b = refl

-- …so applying it twice costs 2 against a static figure of 1: the static count
-- is not an upper bound.
closure-twice : ∀ {A B} (a : ⟦ A ⟧C) (b : ⟦ B ⟧C) →
                (snd (fst (Lᶜ (closT {A} {B}) a) b)
                   +ℕ snd (fst (Lᶜ (closT {A} {B}) a) b))
                ≡ suc (suc zero)
closure-twice a b = refl

------------------------------------------------------------------------
-- ★ DIVERGENCE (d) — `cata`: the algebra runs once per NODE.
-- Functor `One ⊕ Id` (the naturals); the algebra dups on the successor branch.
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

nz : Fix NatF
nz = fix (inj₁ tt)

ns : Fix NatF → Fix NatF
ns n = fix (inj₂ n)

-- alg : LTm (Unit + Unit) Unit — zero-branch free, successor-branch dups once.
natAlg : LTm (⟦ NatF ⟧F Unit) Unit
natAlg = lcase lid (fstL ∘l dup)

cata-static : dupCount (lcata NatF natAlg) ≡ suc zero
cata-static = refl

-- a 3-node tree (two successors) pays TWO allocations: once per successor node.
cata-under : snd (Lᶜ (lcata NatF natAlg) (ns (ns nz))) ≡ suc (suc zero)
cata-under = refl

-- …and a 1-node tree pays none — the figure depends on the INPUT, so no
-- syntactic count can be correct for both.
cata-zero-nodes : snd (Lᶜ (lcata NatF natAlg) nz) ≡ zero
cata-zero-nodes = refl

------------------------------------------------------------------------
-- ★ OPERATIONAL LINEARITY.
--
-- `DupFree` alone cannot bound a run: `leval`'s input closure is an ARBITRARY
-- semantic value and may report any cost. The fix is the standard one — a
-- logical relation on values, "using this allocates nothing", whose `⇒` case
-- quantifies over `Free` arguments. `μ F` is trivially `Free` because `Func`
-- is `Ty`-independent, so a `Fix F` contains no functions.
------------------------------------------------------------------------

Free : ∀ A → ⟦ A ⟧C → Set
Free Void  ()
Free Unit  x        = ⊤
Free (A * B) (a , b) = Free A a × Free B b
Free (A + B) (inj₁ a) = Free A a
Free (A + B) (inj₂ b) = Free B b
Free (A ⇒ B) f       = (a : ⟦ A ⟧C) → Free A a → Free B (fst (f a)) × (snd (f a) ≡ zero)
Free (μ F) x         = ⊤

-- ★ FOLDING A ZERO-COST ALGEBRA COSTS ZERO — the `cata` analogue of
-- `NbEPLinPass.dupfree-no-alloc`, and the reason (d) above is the ONLY way a
-- fold can allocate: all the cost comes from the algebra, once per node.
-- Phrased directly against the evaluator's `map-cata-Set` (rather than a
-- private copy) so `cataC` unfolds definitionally into the statement.
cata-free : ∀ F {X : Set} (alg : ⟦ F ⟧FS X → X × ℕ) →
            (∀ w → snd (alg w) ≡ zero) →
            ∀ (x : Fix F) → snd (cataC F alg x) ≡ zero
map-free  : ∀ F G {X : Set} (alg : ⟦ F ⟧FS X → X × ℕ) →
            (∀ w → snd (alg w) ≡ zero) →
            ∀ (y : ⟦ G ⟧FS (Fix F)) →
            snd (sumF G (map-cata-Set F G (cataStep F alg) y)) ≡ zero

cata-free F alg h (fix w) =
  cong₂ _+ℕ_ (map-free F F alg h w)
             (h (fst (sumF F (map-cata-Set F F (cataStep F alg) w))))

map-free F Id      alg h y        = cata-free F alg h y
map-free F One     alg h y        = refl
map-free F (Kc _)  alg h y        = refl
map-free F (G ⊕ H) alg h (inj₁ y) = map-free F G alg h y
map-free F (G ⊕ H) alg h (inj₂ z) = map-free F H alg h z
map-free F (G ⊗ H) alg h (y , z)  =
  cong₂ _+ℕ_ (map-free F G alg h y) (map-free F H alg h z)

-- `Free` lifted through a functor, and its transport across the coherence.
-- (`Kc G` is a `Fix G`, so it is `Free` for the same reason `μ F` is.)
FreeG : ∀ G {X : Ty} → ⟦ G ⟧FS ⟦ X ⟧C → Set
FreeG Id      {X} v        = Free X v
FreeG One         _        = ⊤
FreeG (Kc _)      _        = ⊤
FreeG (G ⊕ H)     (inj₁ y) = FreeG G y
FreeG (G ⊕ H)     (inj₂ z) = FreeG H z
FreeG (G ⊗ H)     (y , z)  = FreeG G y × FreeG H z

freeCoh : ∀ G X (v : ⟦ G ⟧FS ⟦ X ⟧C) → FreeG G {X} v → Free (⟦ G ⟧F X) (cohC⁻¹ G X v)
freeCoh Id      X v        fv        = fv
freeCoh One     X v        fv        = tt
freeCoh (Kc G)  X v        fv        = tt
freeCoh (G ⊕ H) X (inj₁ y) fv        = freeCoh G X y fv
freeCoh (G ⊕ H) X (inj₂ z) fv        = freeCoh H X z fv
freeCoh (G ⊗ H) X (y , z)  (fy , fz) = (freeCoh G X y fy , freeCoh H X z fz)

-- The fold preserves `Free` and stays free of cost, given an algebra that does.
-- (The `∀ w` version `cata-free` above is too strong to obtain from the
-- induction: `alg` is only ever applied to values the fold itself built, which
-- are `Free` — so the hypothesis has to be relativised to `FreeG`.)
cata-ok : ∀ F {X : Ty} (alg : ⟦ F ⟧FS ⟦ X ⟧C → ⟦ X ⟧C × ℕ) →
          (∀ w → FreeG F {X} w → Free X (fst (alg w)) × (snd (alg w) ≡ zero)) →
          ∀ (x : Fix F) → Free X (fst (cataC F alg x)) × (snd (cataC F alg x) ≡ zero)
map-ok  : ∀ F G {X : Ty} (alg : ⟦ F ⟧FS ⟦ X ⟧C → ⟦ X ⟧C × ℕ) →
          (∀ w → FreeG F {X} w → Free X (fst (alg w)) × (snd (alg w) ≡ zero)) →
          ∀ (y : ⟦ G ⟧FS (Fix F)) →
          FreeG G {X} (fst (sumF G (map-cata-Set F G (cataStep F alg) y)))
          × (snd (sumF G (map-cata-Set F G (cataStep F alg) y)) ≡ zero)

cata-ok F alg h (fix w) =
  ( fst (h (fst (sumF F (map-cata-Set F F (cataStep F alg) w))) (fst (map-ok F F alg h w)))
  , cong₂ _+ℕ_ (snd (map-ok F F alg h w))
               (snd (h (fst (sumF F (map-cata-Set F F (cataStep F alg) w)))
                       (fst (map-ok F F alg h w)))) )

map-ok F Id      alg h y        = cata-ok F alg h y
map-ok F One     alg h y        = (tt , refl)
map-ok F (Kc _)  alg h y        = (tt , refl)
map-ok F (G ⊕ H) alg h (inj₁ y) = map-ok F G alg h y
map-ok F (G ⊕ H) alg h (inj₂ z) = map-ok F H alg h z
map-ok F (G ⊗ H) alg h (y , z)  =
  ( (fst (map-ok F G alg h y) , fst (map-ok F H alg h z))
  , cong₂ _+ℕ_ (snd (map-ok F G alg h y)) (snd (map-ok F H alg h z)) )

------------------------------------------------------------------------
-- ★ OPERATIONAL LINEARITY: a `DupFree` morphism, run on `Free` inputs,
-- performs ZERO allocations and returns a `Free` result.
--
-- This is `NbEPLinPass.dupfree-no-alloc` upgraded from a statement about
-- SYNTAX (the term contains no `dup` generator) to one about EXECUTION (the
-- run performs no allocation) — which is what "the linear sublanguage
-- allocates nothing" has to mean for the memory-management dividend to hold.
-- Note where the `Free` hypothesis is actually consumed: only at `leval`,
-- exactly the case that motivated the logical relation.
------------------------------------------------------------------------

dyn-linear : ∀ {A B} {f : LTm A B} → DupFree f → (x : ⟦ A ⟧C) → Free A x →
             Free B (fst (Lᶜ f x)) × (snd (Lᶜ f x) ≡ zero)
dyn-linear df-id           x        fx        = (fx , refl)
dyn-linear (df-∘ p q)      x        fx        =
  ( fst (dyn-linear p _ (fst (dyn-linear q x fx)))
  , cong₂ _+ℕ_ (snd (dyn-linear q x fx))
               (snd (dyn-linear p _ (fst (dyn-linear q x fx)))) )
dyn-linear (df-⊗ p q)      (a , b)  (fa , fb) =
  ( ( fst (dyn-linear p a fa) , fst (dyn-linear q b fb) )
  , cong₂ _+ℕ_ (snd (dyn-linear p a fa))
               (cong₂ _+ℕ_ (snd (dyn-linear q b fb)) refl) )
dyn-linear df-ρl           (a , tt) (fa , _)  = (fa , refl)
dyn-linear df-ρl⁻          a        fa        = ((fa , tt) , refl)
dyn-linear df-lul          (tt , a) (_ , fa)  = (fa , refl)
dyn-linear df-lul⁻         a        fa        = ((tt , fa) , refl)
dyn-linear df-lassoc  ((a , b) , c) ((fa , fb) , fc) = ((fa , (fb , fc)) , refl)
dyn-linear df-lassoc⁻ (a , (b , c)) (fa , (fb , fc)) = (((fa , fb) , fc) , refl)
dyn-linear df-lswap        (a , b)  (fa , fb) = ((fb , fa) , refl)
dyn-linear df-drop         a        fa        = (tt , refl)
dyn-linear df-linl         a        fa        = (fa , refl)
dyn-linear df-linr         b        fb        = (fb , refl)
dyn-linear (df-case p q)   (inj₁ a) fa        = dyn-linear p a fa
dyn-linear (df-case p q)   (inj₂ b) fb        = dyn-linear q b fb
dyn-linear df-In           x        fx        = (tt , refl)
dyn-linear (df-cata F p)   x        fx        =
  cata-ok F _ (λ w fw → dyn-linear p (cohC⁻¹ F _ w) (freeCoh F _ w fw)) x
-- building a closure costs nothing, and the closure IS `Free` — precisely
-- because its body is `DupFree`, which is what `df-lcurry` records.
dyn-linear (df-lcurry p)   a        fa        =
  ( (λ b fb → dyn-linear p (a , b) (fa , fb)) , refl )
-- ★ the case the logical relation exists for: the cost of applying a closure
-- is whatever the closure reports, and `Free` is exactly the hypothesis that
-- bounds it.
dyn-linear df-leval        (f , a)  (ff , fa) = ff a fa

------------------------------------------------------------------------
-- ★ END-TO-END, and the honest form of the memory dividend.
--
-- Composing with `NbEPLinPass.pass-df`: a PAIRING-FREE cartesian source
-- compiles to a program that performs NO ALLOCATION AT RUNTIME. Together with
-- the divergences above, this is the accurate statement of the linearization
-- payoff:
--
--   · pairing-free source  ⇒ zero allocations, as a theorem about RUNS;
--   · otherwise            ⇒ the figure depends on the run (branch taken, tree
--                            size, application count) and `dupCount` is the
--                            right SYNTACTIC invariant but not a bound.
------------------------------------------------------------------------

pass-dyn : ∀ {A B} {f : Term A B} {p : FO f} → PairFree p →
           (x : ⟦ A ⟧C) → Free A x →
           Free B (fst (Lᶜ L⟦ p ⟧ x)) × (snd (Lᶜ L⟦ p ⟧ x) ≡ zero)
pass-dyn pf x fx = dyn-linear (pass-df pf) x fx
