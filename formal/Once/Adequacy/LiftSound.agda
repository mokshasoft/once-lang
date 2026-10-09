-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.LiftSound — A LIFTED ARITH BLOCK MEANS THE SUBTREE IT
-- REPLACED (D165, for `RewritePreserves`).
--
-- The recogniser reads an IR subtree as an arithmetic expression over the
-- input: compiler primitives (`primV`, D255, whose meaning IS the operation),
-- literals, and input paths through environment plumbing. Each piece's meaning
-- is a value and no event, and the value is the block's (`block-semM`) at the
-- input. The recursion follows the recogniser's own (its re-association is
-- the monad's associativity), by a measure that re-association decreases.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.DenotTrace using (CallEnv)

module Once.Adequacy.LiftSound (fmt : TargetNum) (ρ : CallEnv) where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.IR
open import Once.IRTy using (⌊_⌋; fits-int; fits-float)
import Once.IRTy as II
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.ValueDomain using (forgetᵇ; cohᴰ; ⟦_⟧ᴰᴵ)
-- The surface base witnesses (the IR's own `base-*` are in scope from `Once.IR`).
open import Once.Functor.Translate using () renaming (base-Prod to b-Prod; base-Int to b-Int; base-Float to b-Float)
open import Once.Arith.Machine.IR using (MArithIR; shape-as-type; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.SigOp.Block using (block-semM; readLeafM; block-info; shape-as-type-base)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Arith.Machine.Rewrite using (try-lift; shape-of; has-op; block-as-ir)
open import Once.Postulates using (extensionality)
open import Data.Maybe using () renaming (map to mapᴹ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Arith.Machine.Shape using (InputShape; shape-int; shape-float; shape-pair; Fst; Snd; InputPath; Path; here-int; here-flt; go-fst; go-snd; typePath?)
open import Once.Arith.Machine.Recognise using (plumbing?; recognise-path-through; rp-at; rp-comp; pair-path;
  PView; pv-id; pv-fst; pv-snd; pv-pair; pv-comp; pv-other; p-view; is-terminal?; TView; tv-term; tv-comp; tv-other; t-view; it-at;
  recognise-body; recognise-binop; recognise-prim; binop-at; rb-at; rb-view; RBView; v-reassoc; v-sigop; v-cint; v-cflt; v-other;
  recognise-body-float; recognise-binop-float; recognise-prim-float; binop-at-float; rbf-at;
  lit-at; flit-at; path-at; binop; unop; recognise-path; rbin-at; rbinf-at; b-view; BView; bv-pair; bv-dist; bv-id; bv-other; pair-of)
open import Once.SigOp.Info using (SigOpSem; mk-info'; primV; SigOpInfo)
open import Once.Arith.Prim using (ArithPrim; primSem; p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f)
import Once.Type as Ty
open import Once.Target.Arch using (module TargetNum)
open TargetNum using (int-bits; float-format)
import Once.Word as OnceWord
import Once.Float.Arith
module W (tn : TargetNum) = OnceWord.Width (int-bits tn)
open import Once.Denotation.TraceMonad using (>>=T-assoc; >>=T-identityˡ)

------------------------------------------------------------------------
-- (a) Plumbing means a value and no event.
------------------------------------------------------------------------

∧-l : ∀ {a b : Bool} → a ∧ b ≡ true → a ≡ true
∧-l {true} _ = refl

∧-r : ∀ {a b : Bool} → a ∧ b ≡ true → b ≡ true
∧-r {true} e = e

Val : ∀ {X Y} → IR X Y → Set
Val {X} {Y} g = ∀ (a : ⟦ X ⟧ᴰᴵ) → Σ (⟦ Y ⟧ᴰᴵ) (λ b → evalᴰ fmt ρ g a ≡ returnT b)

plumbing-val : ∀ {X Y} (g : IR X Y) → plumbing? g ≡ true → Val g
plumbing-val id       _ a = a , refl
plumbing-val fst      _ a = proj₁ a , refl
plumbing-val snd      _ a = proj₂ a , refl
plumbing-val terminal _ a = tt , refl
plumbing-val ⟨ f , g ⟩ e a with plumbing-val f (∧-l e) a | plumbing-val g (∧-r {plumbing? f} e) a
... | b , eb | c , ec =
  (b , c) , trans (cong (λ m → m >>=T λ b′ → evalᴰ fmt ρ g a >>=T λ c′ → returnT (b′ , c′)) eb)
                  (cong (λ m → m >>=T λ c′ → returnT (b , c′)) ec)
plumbing-val (f ∘ g) e a with plumbing-val g (∧-r {plumbing? f} e) a
... | c , ec with plumbing-val f (∧-l e) c
...   | b , eb = b , trans (cong (λ m → m >>=T evalᴰ fmt ρ f) ec) eb

------------------------------------------------------------------------
-- (b) An input path reads a leaf of the input.
------------------------------------------------------------------------

-- Reading a path on an IR value: a leaf of `Int`/`Float` kind, through pairs.
rd : InputPath → ∀ (X : II.IRTy) → ⟦ X ⟧ᴰᴵ → Maybe Carrier
rd []        II.Int     v       = just v
rd []        II.Float   v       = just v
rd (Fst ∷ p) (X II.* Y) (x , y) = rd p X x
rd (Snd ∷ p) (X II.* Y) (x , y) = rd p Y y
{-# CATCHALL #-}
rd _         _          _       = nothing

PathAt : ∀ {X Y} → IR X Y → InputPath → InputPath → ⟦ X ⟧ᴰᴵ → Set
PathAt {X} {Y} m p₀ p a = Σ (⟦ Y ⟧ᴰᴵ) (λ b → (evalᴰ fmt ρ m a ≡ returnT b) × (rd p₀ Y b ≡ rd p X a))

PathOK : ∀ {X Y} → IR X Y → InputPath → InputPath → Set
PathOK {X} {Y} m p₀ p = ∀ (a : ⟦ X ⟧ᴰᴵ) → PathAt m p₀ p a

path-sound : ∀ {X Y} (m : IR X Y) (p₀ p : InputPath) → recognise-path-through m p₀ ≡ just p → PathOK m p₀ p
path-ok    : ∀ {X Y} (m : IR X Y) (v : PView m) (p₀ p : InputPath) → rp-at m v p₀ ≡ just p → PathOK m p₀ p

path-sound m p₀ p eq = path-ok m (p-view m) p₀ p eq

path-ok .id  pv-id  p₀ .p₀ refl a = a , refl , refl
path-ok .fst pv-fst p₀ ._  refl a = proj₁ a , refl , refl
path-ok .snd pv-snd p₀ ._  refl a = proj₂ a , refl , refl
path-ok .(⟨ x , y ⟩) (pv-pair x y) (Fst ∷ p₀) p eq a = pair-l (plumbing? y) refl eq
  where
    pair-l : ∀ (b : Bool) → plumbing? y ≡ b → pair-path b x p₀ ≡ just p → PathAt ⟨ x , y ⟩ (Fst ∷ p₀) p a
    pair-l true  py eq′ with path-sound x p₀ p eq′ a | plumbing-val y py a
    ... | b , eb , rb | c , ec =
      (b , c) , trans (cong (λ m → m >>=T λ b′ → evalᴰ fmt ρ y a >>=T λ c′ → returnT (b′ , c′)) eb)
                      (cong (λ m → m >>=T λ c′ → returnT (b , c′)) ec)
              , rb
    pair-l false py ()
path-ok .(⟨ x , y ⟩) (pv-pair x y) (Snd ∷ p₀) p eq a = pair-r (plumbing? x) refl eq
  where
    pair-r : ∀ (b : Bool) → plumbing? x ≡ b → pair-path b y p₀ ≡ just p → PathAt ⟨ x , y ⟩ (Snd ∷ p₀) p a
    pair-r true  px eq′ with plumbing-val x px a | path-sound y p₀ p eq′ a
    ... | b , eb | c , ec , rc =
      (b , c) , trans (cong (λ m → m >>=T λ b′ → evalᴰ fmt ρ y a >>=T λ c′ → returnT (b′ , c′)) eb)
                      (cong (λ m → m >>=T λ c′ → returnT (b , c′)) ec)
              , rc
    pair-r false px ()
path-ok .(⟨ x , y ⟩) (pv-pair x y) [] p () a
path-ok .(f ∘ g) (pv-comp f g) p₀ p eq a = comp (recognise-path-through f p₀) refl eq
  where
    comp : ∀ (r : Maybe InputPath) → recognise-path-through f p₀ ≡ r → rp-comp g r ≡ just p → PathAt (f ∘ g) p₀ p a
    comp (just pf) ef eg with path-sound g pf p eg a
    ... | c , ec , rc with path-sound f p₀ pf ef c
    ...   | b , eb , rb = b , trans (cong (λ m → m >>=T evalᴰ fmt ρ f) ec) eb , trans rb rc
    comp nothing ef ()
path-ok m (pv-other m) p₀ p () a

------------------------------------------------------------------------
-- (c) The input, read at a typed path, is the block's leaf.
------------------------------------------------------------------------

-- The input as the block reads it — exactly the argument `evalᴰ` hands a SigOp
-- (transported to the surface type, then read as the first-order value).
toM : ∀ (sh : InputShape) → ⟦ ⌊ shape-as-type sh ⌋ ⟧ᴰᴵ → M.⟦ shape-as-type sh ⟧
toM sh a = forgetᵇ (shape-as-type-base sh) (subst (λ z → z) (cohᴰ (shape-as-type sh)) a)

private
  subst-× : ∀ {X X′ Y Y′ : Set} (p : X ≡ X′) (q : Y ≡ Y′) (u : X) (v : Y)
          → subst (λ z → z) (cong₂ _×_ p q) (u , v) ≡ (subst (λ z → z) p u , subst (λ z → z) q v)
  subst-× refl refl u v = refl

toM-pair : ∀ (l r : InputShape) (x : ⟦ ⌊ shape-as-type l ⌋ ⟧ᴰᴵ) (y : ⟦ ⌊ shape-as-type r ⌋ ⟧ᴰᴵ)
         → toM (shape-pair l r) (x , y) ≡ (toM l x , toM r y)
toM-pair l r x y =
  cong (forgetᵇ (shape-as-type-base (shape-pair l r))) (subst-× (cohᴰ (shape-as-type l)) (cohᴰ (shape-as-type r)) x y)

leaf-sound : ∀ (sh : InputShape) (n : NumType) (p : InputPath) (tp : Path sh n) → typePath? sh n p ≡ just tp
           → ∀ (a : ⟦ ⌊ shape-as-type sh ⌋ ⟧ᴰᴵ) → rd p ⌊ shape-as-type sh ⌋ a ≡ just (readLeafM tp (toM sh a))
leaf-sound shape-int   NInt   [] .here-int refl a = refl
leaf-sound shape-float NFloat [] .here-flt refl a = refl
leaf-sound (shape-pair l r) n (Fst ∷ p) tp eq (x , y) = go (typePath? l n p) refl eq
  where
    go : ∀ (m : Maybe (Path l n)) → typePath? l n p ≡ m → mapᴹ go-fst m ≡ just tp
       → rd p ⌊ shape-as-type l ⌋ x ≡ just (readLeafM tp (toM (shape-pair l r) (x , y)))
    go (just tp′) e refl = trans (leaf-sound l n p tp′ e x) (cong (λ v → just (readLeafM (go-fst tp′) v)) (sym (toM-pair l r x y)))
    go nothing    e ()
leaf-sound (shape-pair l r) n (Snd ∷ p) tp eq (x , y) = go (typePath? r n p) refl eq
  where
    go : ∀ (m : Maybe (Path r n)) → typePath? r n p ≡ m → mapᴹ go-snd m ≡ just tp
       → rd p ⌊ shape-as-type r ⌋ y ≡ just (readLeafM tp (toM (shape-pair l r) (x , y)))
    go (just tp′) e refl = trans (leaf-sound r n p tp′ e y) (cong (λ v → just (readLeafM (go-snd tp′) v)) (sym (toM-pair l r x y)))
    go nothing    e ()

------------------------------------------------------------------------
-- (d) The measure the recogniser's recursion decreases (its re-association
-- included).
------------------------------------------------------------------------

sz : ∀ {A B} → IR A B → ℕ
sz (f ∘ g)     = suc (sz f + sz f + sz g)
sz ⟨ f , g ⟩   = suc (sz f + sz g)
{-# CATCHALL #-}
sz _           = 1

private
  ≤-+ʳ : ∀ (m n : ℕ) → m ≤ n + m
  ≤-+ʳ m n = m≤n+m m n

  reassoc-< : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) → sz (f ∘ (g ∘ h)) < sz ((f ∘ g) ∘ h)
  reassoc-< f g h = s≤s (s≤s (bound (sz f) (sz g) (sz h)))
    where
      open import Data.Nat.Properties using (+-assoc)
      bound : ∀ F G H → F + F + suc (G + G + H) ≤ F + F + G + suc (F + F + G) + H
      bound F G H = Data.Nat.Properties.≤-trans
        (Data.Nat.Properties.≤-reflexive (lhs≡ F G H))
        (Data.Nat.Properties.≤-trans (step F G H) (Data.Nat.Properties.≤-reflexive (sym (rhs≡ F G H))))
        where
          open import Data.Nat.Tactic.RingSolver
          lhs≡ : ∀ F G H → F + F + suc (G + G + H) ≡ suc (F + F + G + G + H)
          lhs≡ = solve-∀
          rhs≡ : ∀ F G H → F + F + G + suc (F + F + G) + H ≡ suc (F + F + G + G + H + F + F)
          rhs≡ = solve-∀
          step : ∀ F G H → suc (F + F + G + G + H) ≤ suc (F + F + G + G + H + F + F)
          step F G H = s≤s (Data.Nat.Properties.≤-trans (m≤m+n (F + F + G + G + H) (F + F))
                                         (Data.Nat.Properties.≤-reflexive (sym (+-assoc (F + F + G + G + H) F F))))

------------------------------------------------------------------------
-- (e) THE RECOGNISED SUBTREE MEANS THE BLOCK.
------------------------------------------------------------------------

private
  -- re-association is the monad's associativity
  assoc : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z)
        → (m >>=T λ x → f x >>=T g) ≡ ((m >>=T f) >>=T g)
  assoc m f g = sym (>>=T-assoc m f g)

  <-≤ : ∀ {a b c : ℕ} → a < b → b ≤ c → a < c
  <-≤ p q = Data.Nat.Properties.<-≤-trans p q

  -- `sz` bounds, all by unfolding
  sz-sigop : ∀ {X Y A} (si : SigOpInfo X Y) (e : IR A ⌊ X ⌋) → sz e < sz (SigOp si ∘ e)
  sz-sigop si e = s≤s (Data.Nat.Properties.≤-trans (Data.Nat.Properties.n≤1+n _) (Data.Nat.Properties.n≤1+n _))

  sz-pairˡ : ∀ {A B C} (a : IR A B) (b : IR A C) → sz a < sz ⟨ a , b ⟩
  sz-pairˡ a b = s≤s (m≤m+n (sz a) (sz b))

  sz-pairʳ : ∀ {A B C} (a : IR A B) (b : IR A C) → sz b < sz ⟨ a , b ⟩
  sz-pairʳ a b = s≤s (m≤n+m (sz b) (sz a))

  sz-distˡ : ∀ {A B C W} (a : IR A B) (b : IR A C) (h : IR W A) → sz (a ∘ h) < sz (⟨ a , b ⟩ ∘ h)
  sz-distˡ a b h = s≤s (s≤s (go (sz a) (sz b) (sz h)))
    where
      open import Data.Nat.Tactic.RingSolver
      e : ∀ X Y H → X + X + H + suc (Y + Y) ≡ X + Y + suc (X + Y) + H
      e = solve-∀
      go : ∀ X Y H → X + X + H ≤ X + Y + suc (X + Y) + H
      go X Y H = Data.Nat.Properties.≤-trans (m≤m+n (X + X + H) (suc (Y + Y)))
                   (Data.Nat.Properties.≤-reflexive (e X Y H))

  sz-distʳ : ∀ {A B C W} (a : IR A B) (b : IR A C) (h : IR W A) → sz (b ∘ h) < sz (⟨ a , b ⟩ ∘ h)
  sz-distʳ a b h = s≤s (s≤s (go (sz a) (sz b) (sz h)))
    where
      open import Data.Nat.Tactic.RingSolver
      e : ∀ X Y H → Y + Y + H + suc (X + X) ≡ X + Y + suc (X + Y) + H
      e = solve-∀
      go : ∀ X Y H → Y + Y + H ≤ X + Y + suc (X + Y) + H
      go X Y H = Data.Nat.Properties.≤-trans (m≤m+n (Y + Y + H) (suc (X + X)))
                   (Data.Nat.Properties.≤-reflexive (e X Y H))

  -- a literal's right-hand side means `tt` and no event
  term-at : ∀ {X} (rhs : IR X II.Unit) (v : TView rhs) → it-at rhs v ≡ true → ∀ a → evalᴰ fmt ρ rhs a ≡ returnT tt
  term-at .terminal       tv-term     _ a = refl
  term-at .(terminal ∘ g) (tv-comp {Z = Z} g) e a with plumbing-val g e a
  ... | c , ec = trans (cong (λ (m : T ⟦ Z ⟧ᴰᴵ) → m >>=T evalᴰ fmt ρ (terminal {Z})) ec)
                       (>>=T-identityˡ c (evalᴰ fmt ρ (terminal {Z})))
  term-at rhs (tv-other rhs) () a

  term-val : ∀ {X} (rhs : IR X II.Unit) → is-terminal? rhs ≡ true → ∀ a → evalᴰ fmt ρ rhs a ≡ returnT tt
  term-val rhs = term-at rhs (t-view rhs)

  -- a pair of values
  -- after a step that returns `c`, the composite means its head at `c`
  through : ∀ {W X Z} {h : IR W X} {a : ⟦ W ⟧ᴰᴵ} {c : ⟦ X ⟧ᴰᴵ} → evalᴰ fmt ρ h a ≡ returnT c
          → (f : IR X Z) {b : ⟦ Z ⟧ᴰᴵ} → evalᴰ fmt ρ (f ∘ h) a ≡ returnT b → evalᴰ fmt ρ f c ≡ returnT b
  through {h = h} {a} {c} ec f e =
    trans (sym (>>=T-identityˡ c (evalᴰ fmt ρ f)))
          (trans (sym (cong (λ m → m >>=T evalᴰ fmt ρ f) ec)) e)

  pair-val : ∀ {X Y Z} (x : IR X Y) (y : IR X Z) (a : ⟦ X ⟧ᴰᴵ) {bx by}
           → evalᴰ fmt ρ x a ≡ returnT bx → evalᴰ fmt ρ y a ≡ returnT by
           → evalᴰ fmt ρ ⟨ x , y ⟩ a ≡ returnT (bx , by)
  pair-val x y a {bx} ex ey =
    trans (cong (λ m → m >>=T λ b′ → evalᴰ fmt ρ y a >>=T λ c′ → returnT (b′ , c′)) ex)
          (cong (λ m → m >>=T λ c′ → returnT (bx , c′)) ey)

BodyAt : ∀ (sh : InputShape) {B} → IR ⌊ shape-as-type sh ⌋ B → ∀ {n} → MArithIR sh n → ⟦ ⌊ shape-as-type sh ⌋ ⟧ᴰᴵ → Set
BodyAt sh {B} ir body a =
  Σ (⟦ B ⟧ᴰᴵ) (λ b → (evalᴰ fmt ρ ir a ≡ returnT b) × (rd [] B b ≡ just (block-semM body fmt (toM sh a))))

BinAt : ∀ (sh : InputShape) {Y} → IR ⌊ shape-as-type sh ⌋ Y → ∀ {n} → MArithIR sh n → MArithIR sh n
      → ⟦ ⌊ shape-as-type sh ⌋ ⟧ᴰᴵ → Set
BinAt sh {Y} e ra rb a =
  Σ (⟦ Y ⟧ᴰᴵ) (λ b → (evalᴰ fmt ρ e a ≡ returnT b)
                   × (rd (Fst ∷ []) Y b ≡ just (block-semM ra fmt (toM sh a)))
                   × (rd (Snd ∷ []) Y b ≡ just (block-semM rb fmt (toM sh a))))

------------------------------------------------------------------------
-- integer kind
------------------------------------------------------------------------

body-sound : ∀ (k : ℕ) (sh : InputShape) {B} (ir : IR ⌊ shape-as-type sh ⌋ B) → sz ir < k
           → ∀ {body} → recognise-body sh ir ≡ just body → ∀ a → BodyAt sh ir body a
body-at    : ∀ (k : ℕ) (sh : InputShape) {B} (ir : IR ⌊ shape-as-type sh ⌋ B) (v : RBView ir) → sz ir < suc k
           → ∀ {body} → rb-at sh ir v ≡ just body → ∀ a → BodyAt sh ir body a
sig-at     : ∀ (k : ℕ) (sh : InputShape) {X Y} nm (s : SigOpSem X Y) bA cB (e : IR ⌊ shape-as-type sh ⌋ ⌊ X ⌋) → sz e < k
           → ∀ {body} → recognise-prim sh s e ≡ just body → ∀ a → BodyAt sh (SigOp (mk-info' nm s bA cB) ∘ e) body a
bin-case   : ∀ (k : ℕ) (sh : InputShape) nm (p : ArithPrim (Ty.Int Ty.* Ty.Int) Ty.Int)
               (c : MArithIR sh NInt → MArithIR sh NInt → MArithIR sh NInt)
           → (∀ ra rb inp → block-semM (c ra rb) fmt inp ≡ primSem p fmt (block-semM ra fmt inp , block-semM rb fmt inp))
           → (e : IR ⌊ shape-as-type sh ⌋ (II.Int II.* II.Int)) → sz e < k
           → ∀ {body} → (r : Maybe _) → recognise-binop sh e ≡ r → binop c r ≡ just body
           → ∀ a → BodyAt sh (SigOp (mk-info' nm (primV p) (b-Prod b-Int b-Int) b-Int) ∘ e) body a
bin-sound  : ∀ (k : ℕ) (sh : InputShape) {Y} (e : IR ⌊ shape-as-type sh ⌋ Y) → sz e < k
           → ∀ {ra rb} → recognise-binop sh e ≡ just (ra , rb) → ∀ a → BinAt sh e ra rb a
bin-at     : ∀ (k : ℕ) (sh : InputShape) {Y} (e : IR ⌊ shape-as-type sh ⌋ Y) (v : BView e) → sz e < k
           → ∀ {ra rb} → rbin-at sh e v ≡ just (ra , rb) → ∀ a → BinAt sh e ra rb a

body-sound zero    sh ir ()
body-sound (suc k) sh ir lt eq a = body-at k sh ir (rb-view ir) lt eq a

body-at k sh .((f ∘ g) ∘ h) (v-reassoc f g h) lt eq a
  with body-sound k sh (f ∘ (g ∘ h)) (<-≤ (reassoc-< f g h) (Data.Nat.Properties.≤-pred lt)) eq a
... | b , eb , rb = b , trans (assoc (evalᴰ fmt ρ h a) (evalᴰ fmt ρ g) (evalᴰ fmt ρ f)) eb , rb
body-at k sh .(SigOp (mk-info' nm s bA cB) ∘ e) (v-sigop (mk-info' nm s bA cB) e) lt eq a =
  sig-at k sh nm s bA cB e (<-≤ (sz-sigop (mk-info' nm s bA cB) e) (Data.Nat.Properties.≤-pred lt)) eq a
body-at k sh .(const fits-int v ∘ rhs) (v-cint v rhs) lt eq a = lit (is-terminal? rhs) refl eq
  where
    lit : ∀ (t : Bool) → is-terminal? rhs ≡ t → ∀ {body} → lit-at t v ≡ just body → BodyAt sh (const fits-int v ∘ rhs) body a
    lit true et refl = _ , cong (λ m → m >>=T evalᴰ fmt ρ (const fits-int v)) (term-val rhs et a) , refl
body-at k sh ir (v-other ir) lt eq a = path (recognise-path ir) refl eq
  where
    path : ∀ (r : Maybe InputPath) → recognise-path ir ≡ r → ∀ {body} → path-at sh NInt r ≡ just body → BodyAt sh ir body a
    path (just p) ep {body} eq′ = typed (typePath? sh NInt p) refl eq′
      where
        typed : ∀ (m : Maybe (Path sh NInt)) → typePath? sh NInt p ≡ m → unop ainput m ≡ just body → BodyAt sh ir body a
        typed (just tp) et refl with path-sound ir [] p ep a
        ... | b , eb , rb = b , eb , trans rb (leaf-sound sh NInt p tp et a)

sig-at k sh nm (primV p-add) (b-Prod b-Int b-Int) b-Int e lt eq a = bin-case k sh nm p-add aadd (λ _ _ _ → refl) e lt _ refl eq a
sig-at k sh nm (primV p-sub) (b-Prod b-Int b-Int) b-Int e lt eq a = bin-case k sh nm p-sub asub (λ _ _ _ → refl) e lt _ refl eq a
sig-at k sh nm (primV p-mul) (b-Prod b-Int b-Int) b-Int e lt eq a = bin-case k sh nm p-mul amul (λ _ _ _ → refl) e lt _ refl eq a
sig-at k sh nm (primV p-div) (b-Prod b-Int b-Int) b-Int e lt eq a = bin-case k sh nm p-div adiv (λ _ _ _ → refl) e lt _ refl eq a
sig-at k sh nm (primV p-mod) (b-Prod b-Int b-Int) b-Int e lt eq a = bin-case k sh nm p-mod amod (λ _ _ _ → refl) e lt _ refl eq a
sig-at k sh nm (primV p-neg) bA@b-Int cB@b-Int e lt eq a = neg (recognise-body sh e) refl eq
  where
    neg : ∀ (r : Maybe _) → recognise-body sh e ≡ r → ∀ {body} → unop aneg r ≡ just body
        → BodyAt sh (SigOp (mk-info' nm (primV p-neg) bA cB) ∘ e) body a
    neg (just r) er refl with body-sound k sh e lt er a
    ... | b , eb , rb = _ , cong (λ m → m >>=T evalᴰ fmt ρ (SigOp (mk-info' nm (primV p-neg) bA cB))) eb
                          , cong (λ x → just (W.⊝_ fmt x)) (just-injective rb)

bin-case k sh nm p c op e lt (just (ra , rb)) er refl a with bin-sound k sh e lt er a
... | (b₁ , b₂) , eb , r₁ , r₂ =
  _ , cong (λ m → m >>=T evalᴰ fmt ρ (SigOp (mk-info' nm (primV p) (b-Prod b-Int b-Int) b-Int))) eb
    , trans (cong₂ (λ x y → just (primSem p fmt (x , y))) (just-injective r₁) (just-injective r₂))
            (cong just (sym (op ra rb (toM sh a))))

bin-sound k sh e lt eq a = bin-at k sh e (b-view e) lt eq a

bin-at k sh .(⟨ x , y ⟩) (bv-pair x y) lt eq a = pair (recognise-body sh x) refl (recognise-body sh y) refl eq
  where
    pair : ∀ (mx : Maybe _) → recognise-body sh x ≡ mx → ∀ (my : Maybe _) → recognise-body sh y ≡ my
         → ∀ {ra rb} → pair-of mx my ≡ just (ra , rb) → BinAt sh ⟨ x , y ⟩ ra rb a
    pair (just rx) ex (just ry) ey refl
      with body-sound k sh x (Data.Nat.Properties.<-trans (sz-pairˡ x y) lt) ex a
         | body-sound k sh y (Data.Nat.Properties.<-trans (sz-pairʳ x y) lt) ey a
    ... | bx , ebx , rbx | by , eby , rby = (bx , by) , pair-val x y a ebx eby , rbx , rby
bin-at k sh .(⟨ x , y ⟩ ∘ h) (bv-dist x y h) lt eq a = dist (plumbing? h) refl eq
  where
    dist : ∀ (t : Bool) → plumbing? h ≡ t → ∀ {ra rb} → binop-at sh t x y h ≡ just (ra , rb) → BinAt sh (⟨ x , y ⟩ ∘ h) ra rb a
    dist true ph eq′ = pair (recognise-body sh (x ∘ h)) refl (recognise-body sh (y ∘ h)) refl eq′
      where
        pair : ∀ (mx : Maybe _) → recognise-body sh (x ∘ h) ≡ mx → ∀ (my : Maybe _) → recognise-body sh (y ∘ h) ≡ my
             → ∀ {ra rb} → pair-of mx my ≡ just (ra , rb) → BinAt sh (⟨ x , y ⟩ ∘ h) ra rb a
        pair (just rx) ex (just ry) ey refl
          with plumbing-val h ph a
             | body-sound k sh (x ∘ h) (Data.Nat.Properties.<-trans (sz-distˡ x y h) lt) ex a
             | body-sound k sh (y ∘ h) (Data.Nat.Properties.<-trans (sz-distʳ x y h) lt) ey a
        ... | c , ec | bx , ebx , rbx | by , eby , rby =
          (bx , by)
          , trans (cong (λ m → m >>=T evalᴰ fmt ρ ⟨ x , y ⟩) ec)
                  (trans (>>=T-identityˡ c (evalᴰ fmt ρ ⟨ x , y ⟩))
                         (pair-val x y c (through {h = h} {a = a} ec x ebx) (through {h = h} {a = a} ec y eby)))
          , rbx , rby
bin-at k sh .id bv-id lt eq a = ids (typePath? sh NInt (Fst ∷ [])) refl (typePath? sh NInt (Snd ∷ [])) refl eq
  where
    -- plan 0.108: the operands are the input's own leaves, read where they are.
    ids : ∀ (m₁ : Maybe (Path sh NInt)) → typePath? sh NInt (Fst ∷ []) ≡ m₁
        → ∀ (m₂ : Maybe (Path sh NInt)) → typePath? sh NInt (Snd ∷ []) ≡ m₂
        → ∀ {ra rb} → pair-of (unop ainput m₁) (unop ainput m₂) ≡ just (ra , rb) → BinAt sh id ra rb a
    ids (just t₁) e₁ (just t₂) e₂ refl =
      a , refl , leaf-sound sh NInt (Fst ∷ []) t₁ e₁ a , leaf-sound sh NInt (Snd ∷ []) t₂ e₂ a
    ids (just _) _ nothing _ ()
    ids nothing  _ _       _ ()
bin-at k sh e (bv-other e) lt () a

------------------------------------------------------------------------
-- float kind
------------------------------------------------------------------------

fbody-sound : ∀ (k : ℕ) (sh : InputShape) {B} (ir : IR ⌊ shape-as-type sh ⌋ B) → sz ir < k
           → ∀ {body} → recognise-body-float sh ir ≡ just body → ∀ a → BodyAt sh ir body a
fbody-at    : ∀ (k : ℕ) (sh : InputShape) {B} (ir : IR ⌊ shape-as-type sh ⌋ B) (v : RBView ir) → sz ir < suc k
           → ∀ {body} → rbf-at sh ir v ≡ just body → ∀ a → BodyAt sh ir body a
fsig-at     : ∀ (k : ℕ) (sh : InputShape) {X Y} nm (s : SigOpSem X Y) bA cB (e : IR ⌊ shape-as-type sh ⌋ ⌊ X ⌋) → sz e < k
           → ∀ {body} → recognise-prim-float sh s e ≡ just body → ∀ a → BodyAt sh (SigOp (mk-info' nm s bA cB) ∘ e) body a
fbin-case   : ∀ (k : ℕ) (sh : InputShape) nm (p : ArithPrim (Ty.Float Ty.* Ty.Float) Ty.Float)
               (c : MArithIR sh NFloat → MArithIR sh NFloat → MArithIR sh NFloat)
           → (∀ ra rb inp → block-semM (c ra rb) fmt inp ≡ primSem p fmt (block-semM ra fmt inp , block-semM rb fmt inp))
           → (e : IR ⌊ shape-as-type sh ⌋ (II.Float II.* II.Float)) → sz e < k
           → ∀ {body} → (r : Maybe _) → recognise-binop-float sh e ≡ r → binop c r ≡ just body
           → ∀ a → BodyAt sh (SigOp (mk-info' nm (primV p) (b-Prod b-Float b-Float) b-Float) ∘ e) body a
fbin-sound  : ∀ (k : ℕ) (sh : InputShape) {Y} (e : IR ⌊ shape-as-type sh ⌋ Y) → sz e < k
           → ∀ {ra rb} → recognise-binop-float sh e ≡ just (ra , rb) → ∀ a → BinAt sh e ra rb a
fbin-at     : ∀ (k : ℕ) (sh : InputShape) {Y} (e : IR ⌊ shape-as-type sh ⌋ Y) (v : BView e) → sz e < k
           → ∀ {ra rb} → rbinf-at sh e v ≡ just (ra , rb) → ∀ a → BinAt sh e ra rb a

fbody-sound zero    sh ir ()
fbody-sound (suc k) sh ir lt eq a = fbody-at k sh ir (rb-view ir) lt eq a

fbody-at k sh .((f ∘ g) ∘ h) (v-reassoc f g h) lt eq a
  with fbody-sound k sh (f ∘ (g ∘ h)) (<-≤ (reassoc-< f g h) (Data.Nat.Properties.≤-pred lt)) eq a
... | b , eb , rb = b , trans (assoc (evalᴰ fmt ρ h a) (evalᴰ fmt ρ g) (evalᴰ fmt ρ f)) eb , rb
fbody-at k sh .(SigOp (mk-info' nm s bA cB) ∘ e) (v-sigop (mk-info' nm s bA cB) e) lt eq a =
  fsig-at k sh nm s bA cB e (<-≤ (sz-sigop (mk-info' nm s bA cB) e) (Data.Nat.Properties.≤-pred lt)) eq a
fbody-at k sh .(const fits-float v ∘ rhs) (v-cflt v rhs) lt eq a = lit (is-terminal? rhs) refl eq
  where
    lit : ∀ (t : Bool) → is-terminal? rhs ≡ t → ∀ {body} → flit-at t v ≡ just body → BodyAt sh (const fits-float v ∘ rhs) body a
    lit true et refl = _ , cong (λ m → m >>=T evalᴰ fmt ρ (const fits-float v)) (term-val rhs et a) , refl
fbody-at k sh ir (v-other ir) lt eq a = path (recognise-path ir) refl eq
  where
    path : ∀ (r : Maybe InputPath) → recognise-path ir ≡ r → ∀ {body} → path-at sh NFloat r ≡ just body → BodyAt sh ir body a
    path (just p) ep {body} eq′ = typed (typePath? sh NFloat p) refl eq′
      where
        typed : ∀ (m : Maybe (Path sh NFloat)) → typePath? sh NFloat p ≡ m → unop ainput m ≡ just body → BodyAt sh ir body a
        typed (just tp) et refl with path-sound ir [] p ep a
        ... | b , eb , rb = b , eb , trans rb (leaf-sound sh NFloat p tp et a)

fsig-at k sh nm (primV p-fadd) (b-Prod b-Float b-Float) b-Float e lt eq a = fbin-case k sh nm p-fadd aadd (λ _ _ _ → refl) e lt _ refl eq a
fsig-at k sh nm (primV p-fsub) (b-Prod b-Float b-Float) b-Float e lt eq a = fbin-case k sh nm p-fsub asub (λ _ _ _ → refl) e lt _ refl eq a
fsig-at k sh nm (primV p-fmul) (b-Prod b-Float b-Float) b-Float e lt eq a = fbin-case k sh nm p-fmul amul (λ _ _ _ → refl) e lt _ refl eq a
fsig-at k sh nm (primV p-fdiv) (b-Prod b-Float b-Float) b-Float e lt eq a = fbin-case k sh nm p-fdiv adiv (λ _ _ _ → refl) e lt _ refl eq a
fsig-at k sh nm (primV p-i2f) bA@b-Int cB@b-Float e lt eq a = conv (recognise-body sh e) refl eq
  where
    conv : ∀ (r : Maybe _) → recognise-body sh e ≡ r → ∀ {body} → unop ai2f r ≡ just body
         → BodyAt sh (SigOp (mk-info' nm (primV p-i2f) bA cB) ∘ e) body a
    conv (just r) er refl with body-sound k sh e lt er a
    ... | b , eb , rb = _ , cong (λ m → m >>=T evalᴰ fmt ρ (SigOp (mk-info' nm (primV p-i2f) bA cB))) eb
                          , cong (λ x → just (Once.Float.Arith.i2f (float-format fmt) (W.toℤ fmt x))) (just-injective rb)

fbin-case k sh nm p c op e lt (just (ra , rb)) er refl a with fbin-sound k sh e lt er a
... | (b₁ , b₂) , eb , r₁ , r₂ =
  _ , cong (λ m → m >>=T evalᴰ fmt ρ (SigOp (mk-info' nm (primV p) (b-Prod b-Float b-Float) b-Float))) eb
    , trans (cong₂ (λ x y → just (primSem p fmt (x , y))) (just-injective r₁) (just-injective r₂))
            (cong just (sym (op ra rb (toM sh a))))

fbin-sound k sh e lt eq a = fbin-at k sh e (b-view e) lt eq a

fbin-at k sh .(⟨ x , y ⟩) (bv-pair x y) lt eq a = pair (recognise-body-float sh x) refl (recognise-body-float sh y) refl eq
  where
    pair : ∀ (mx : Maybe _) → recognise-body-float sh x ≡ mx → ∀ (my : Maybe _) → recognise-body-float sh y ≡ my
         → ∀ {ra rb} → pair-of mx my ≡ just (ra , rb) → BinAt sh ⟨ x , y ⟩ ra rb a
    pair (just rx) ex (just ry) ey refl
      with fbody-sound k sh x (Data.Nat.Properties.<-trans (sz-pairˡ x y) lt) ex a
         | fbody-sound k sh y (Data.Nat.Properties.<-trans (sz-pairʳ x y) lt) ey a
    ... | bx , ebx , rbx | by , eby , rby = (bx , by) , pair-val x y a ebx eby , rbx , rby
fbin-at k sh .(⟨ x , y ⟩ ∘ h) (bv-dist x y h) lt eq a = dist (plumbing? h) refl eq
  where
    dist : ∀ (t : Bool) → plumbing? h ≡ t → ∀ {ra rb} → binop-at-float sh t x y h ≡ just (ra , rb) → BinAt sh (⟨ x , y ⟩ ∘ h) ra rb a
    dist true ph eq′ = pair (recognise-body-float sh (x ∘ h)) refl (recognise-body-float sh (y ∘ h)) refl eq′
      where
        pair : ∀ (mx : Maybe _) → recognise-body-float sh (x ∘ h) ≡ mx → ∀ (my : Maybe _) → recognise-body-float sh (y ∘ h) ≡ my
             → ∀ {ra rb} → pair-of mx my ≡ just (ra , rb) → BinAt sh (⟨ x , y ⟩ ∘ h) ra rb a
        pair (just rx) ex (just ry) ey refl
          with plumbing-val h ph a
             | fbody-sound k sh (x ∘ h) (Data.Nat.Properties.<-trans (sz-distˡ x y h) lt) ex a
             | fbody-sound k sh (y ∘ h) (Data.Nat.Properties.<-trans (sz-distʳ x y h) lt) ey a
        ... | c , ec | bx , ebx , rbx | by , eby , rby =
          (bx , by)
          , trans (cong (λ m → m >>=T evalᴰ fmt ρ ⟨ x , y ⟩) ec)
                  (trans (>>=T-identityˡ c (evalᴰ fmt ρ ⟨ x , y ⟩))
                         (pair-val x y c (through {h = h} {a = a} ec x ebx) (through {h = h} {a = a} ec y eby)))
          , rbx , rby
fbin-at k sh .id bv-id lt eq a = ids (typePath? sh NFloat (Fst ∷ [])) refl (typePath? sh NFloat (Snd ∷ [])) refl eq
  where
    -- plan 0.108: the operands are the input's own leaves, read where they are.
    ids : ∀ (m₁ : Maybe (Path sh NFloat)) → typePath? sh NFloat (Fst ∷ []) ≡ m₁
        → ∀ (m₂ : Maybe (Path sh NFloat)) → typePath? sh NFloat (Snd ∷ []) ≡ m₂
        → ∀ {ra rb} → pair-of (unop ainput m₁) (unop ainput m₂) ≡ just (ra , rb) → BinAt sh id ra rb a
    ids (just t₁) e₁ (just t₂) e₂ refl =
      a , refl , leaf-sound sh NFloat (Fst ∷ []) t₁ e₁ a , leaf-sound sh NFloat (Snd ∷ []) t₂ e₂ a
    ids (just _) _ nothing _ ()
    ids nothing  _ _       _ ()
fbin-at k sh e (bv-other e) lt () a

------------------------------------------------------------------------
-- THE LEMMA: a lifted block means the subtree it replaced.
------------------------------------------------------------------------

private
  -- the block SigOp means the block, at the input
  block-int : ∀ (sh : InputShape) (body : MArithIR sh NInt) (a : ⟦ ⌊ shape-as-type sh ⌋ ⟧ᴰᴵ)
            → evalᴰ fmt ρ (SigOp (block-info body)) a ≡ returnT (block-semM body fmt (toM sh a))
  block-int sh body a = refl

  block-flt : ∀ (sh : InputShape) (body : MArithIR sh NFloat) (a : ⟦ ⌊ shape-as-type sh ⌋ ⟧ᴰᴵ)
            → evalᴰ fmt ρ (SigOp (block-info body)) a ≡ returnT (block-semM body fmt (toM sh a))
  block-flt sh body a = refl

  just-int : ∀ {b c : Carrier} → rd [] II.Int b ≡ just c → b ≡ c
  just-int = just-injective

  just-flt : ∀ {b c : Carrier} → rd [] II.Float b ≡ just c → b ≡ c
  just-flt = just-injective

lift-sound : ∀ {A B} (ir ir′ : IR A B) (blk : ArithBlock) → try-lift ir ≡ just (ir′ , blk) → evalᴰ fmt ρ ir′ ≡ evalᴰ fmt ρ ir
lift-sound {A} {II.Int} ir ir′ blk eq with shape-of A
... | just (sh , refl) with recognise-body sh ir in er
...   | just body with has-op body
...     | true with eq
...       | refl = extensionality λ a → with-body (body-sound (suc (sz ir)) sh ir (s≤s ≤-refl) er a)
  where
    with-body : ∀ {a} → BodyAt sh ir body a → evalᴰ fmt ρ (block-as-ir refl body) a ≡ evalᴰ fmt ρ ir a
    with-body {a} (b , eb , rb) = trans (block-int sh body a) (sym (trans eb (cong returnT (just-int rb))))
lift-sound {A} {II.Float} ir ir′ blk eq with shape-of A
... | just (sh , refl) with recognise-body-float sh ir in er
...   | just body with has-op body
...     | true with eq
...       | refl = extensionality λ a → with-body (fbody-sound (suc (sz ir)) sh ir (s≤s ≤-refl) er a)
  where
    with-body : ∀ {a} → BodyAt sh ir body a → evalᴰ fmt ρ (block-as-ir refl body) a ≡ evalᴰ fmt ρ ir a
    with-body {a} (b , eb , rb) = trans (block-flt sh body a) (sym (trans eb (cong returnT (just-flt rb))))
