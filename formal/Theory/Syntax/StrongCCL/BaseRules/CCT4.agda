------------------------------------------------------------------------
-- Theory.Syntax.StrongCCL.BaseRules.CCT4
--
-- Parameterized rules introduced at the CCT4 level (final coalgebras,
-- ν-types). Three rules, grouped as β-rules:
--
--   νout-νin : νOut ∘ νIn ⟶ id
--   νin-νout : νIn ∘ νOut ⟶ id
--   ana-β    : νOut ∘ ana coalg ⟶ fmap F (ana coalg) ∘ coalg
--
-- (Dual to CCT3's cata-β, out-in, in-out.)
------------------------------------------------------------------------

module Theory.Syntax.StrongCCL.BaseRules.CCT4 where

module Rules
  (Ty    : Set)
  (Term  : Ty → Ty → Set)
  (id    : ∀ {A}     → Term A A)
  (_∘_   : ∀ {A B C} → Term B C → Term A B → Term A C)
  (ν     : (Ty → Ty) → Ty)
  (νOut  : ∀ {F : Ty → Ty} → Term (ν F) (F (ν F)))
  (νIn   : ∀ {F : Ty → Ty} → Term (F (ν F)) (ν F))
  (ana   : ∀ {F : Ty → Ty} {A} → Term A (F A) → Term A (ν F))
  (fmap  : ∀ {F : Ty → Ty} {A B} → Term A B → Term (F A) (F B))
  where

  data _⟶β_ : ∀ {A B} → Term A B → Term A B → Set where
    νin-νout : ∀ {F : Ty → Ty} →
               (νIn  {F} ∘ νOut {F}) ⟶β id
    νout-νin : ∀ {F : Ty → Ty} →
               (νOut {F} ∘ νIn  {F}) ⟶β id
    ana-β    : ∀ {F : Ty → Ty} {A} {coalg : Term A (F A)} →
               (νOut {F} ∘ ana {F} coalg) ⟶β
               (fmap {F} (ana {F} coalg) ∘ coalg)

  infix 4 _⟶β_
