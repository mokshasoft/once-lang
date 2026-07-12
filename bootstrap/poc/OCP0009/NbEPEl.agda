------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the Tarski decoder `El : Code → Ty`
--
-- `NbEPCwF` gave the CwF TYPE layer: Π/Σ formers as fragment codes `Tm _ U`
-- and conversion decided by `nf`. This module adds the missing bridge the
-- plan named: a **Tarski decoder** that turns a type-CODE into the actual
-- `Ty` it denotes, so that
--
--   * a context can be EXTENDED by a code (`Γ ▷ᶜ A`, driven by data), and
--   * we get **terms-of-type** `Tmᵗ Γ A = Tm ⟦ Γ ⟧C (El A)`.
--
-- Design (honest about the container ceiling). The type-codes are an ordinary
-- inductive family `Code` — the FIRST-ORDER Tarski universe. Its `Π`/`Σ`
-- formers store two *codes* (`a b : Code`), NOT a code and a family
-- `El a → Code`. A genuinely dependent `Π (x : El a). B x` would need exactly
-- that family — i.e. `U` defined MUTUALLY with `El` (induction-recursion),
-- which OCP-0009 puts out of scope (§D / Rung 4 ceiling / FAQ Q9). So here
-- `El (a `Π b) = El a ⇒ El b` — the CORRECT denotation when `b` does not
-- depend on `x` (non-dependent Π *is* the arrow), and the honest ceiling is
-- that the code language cannot *express* a dependent `b`.
--
-- What is genuinely proven:
--   * `El` decodes every code to a `Ty`;
--   * the reflection `⌜_⌝ : Code → Tm Unit U` lands codes as IR `U`-data,
--     agreeing with `NbEPCwF`'s smart constructors (self-hosting bridge);
--   * `El` and the reflection RESPECT code identity (well-defined on codes);
--   * **`El` WELDED to the NbE-decided conversion** (`El-weld`): equal
--     code-VALUES give equal decoded types, via a left-inverse decoder
--     `decodeV` that round-trips `El` (see its section for the one honest gap
--     — `reifyVal`-injectivity — between value equality and surface `nf`);
--   * code-driven context extension + terms-of-type, with the context
--     variable as a real term `varᶜ`.
--
-- The immediate follow-on (documented, not built): decoding an OPEN code
-- `Tm I U` pointwise gives genuinely INDEXED families (`Vec n`-style) whose
-- fibres are decided by NbE on the index — real dependency WITHOUT IR.
------------------------------------------------------------------------

module poc.OCP0009.NbEPEl where

open import normalizer.Syntax.Types
open import poc.OCP0009.NbEK
  using ( Val; vUnit; vPair; vInl; vInr; vIn )
open import poc.OCP0009.NbEP
  using ( Tm; _⊙_; sndT; idT; case; cataT; nf; eval
        ; NatF; zero; suc; one; two; double )
open import poc.OCP0009.NbEPCwF
  using ( U; UF; Nat
        ; ⌜unit⌝; ⌜nat⌝; Π[_,_]; Σ[_,_]; _⇒C_; _×C_
        ; Ctx; ∙; _▷_; ⟦_⟧C )

------------------------------------------------------------------------
-- The first-order Tarski universe of type-codes.
------------------------------------------------------------------------

infixr 7 _`×_
infixr 6 _`⇒_
data Code : Set where
  `unit `nat : Code
  _`×_ _`⇒_ _`Π_ _`Σ_ : Code → Code → Code

------------------------------------------------------------------------
-- The decoder — a type-code becomes the `Ty` it denotes.
-- `Π`/`Σ` decode to their NON-DEPENDENT meaning (see header): correct when
-- the codomain code does not mention the domain (the only thing first-order
-- codes can express).
------------------------------------------------------------------------

El : Code → Ty
El `unit    = Unit
El `nat     = Nat
El (a `× b) = El a * El b
El (a `⇒ b) = El a ⇒ El b
El (a `Π b) = El a ⇒ El b
El (a `Σ b) = El a * El b

------------------------------------------------------------------------
-- Reflection into the IR universe — codes ARE `U`-data. Agrees with the
-- `NbEPCwF` smart constructors, so a `Code` and its reflection are the same
-- object seen two ways (the self-hosting bridge).
------------------------------------------------------------------------

⌜_⌝ : Code → Tm Unit U
⌜ `unit ⌝  = ⌜unit⌝
⌜ `nat ⌝   = ⌜nat⌝
⌜ a `× b ⌝ = ⌜ a ⌝ ×C ⌜ b ⌝
⌜ a `⇒ b ⌝ = ⌜ a ⌝ ⇒C ⌜ b ⌝
⌜ a `Π b ⌝ = Π[ ⌜ a ⌝ , ⌜ b ⌝ ]
⌜ a `Σ b ⌝ = Σ[ ⌜ a ⌝ , ⌜ b ⌝ ]

------------------------------------------------------------------------
-- Well-definedness: both `El` and the reflection respect code identity.
------------------------------------------------------------------------

El-cong : ∀ {c d} → c ≡ d → El c ≡ El d
El-cong refl = refl

reflect-cong : ∀ {c d} → c ≡ d → nf ⌜ c ⌝ ≡ nf ⌜ d ⌝
reflect-cong refl = refl

------------------------------------------------------------------------
-- WELDING `El` TO THE NbE-DECIDED CONVERSION (the load-bearing direction).
--
-- A checker decides code-conversion by NbE; to transport along it, it needs
-- `El c ≡ El d`. We prove exactly that, keyed on the NbE VALUE of the code.
--
-- The route is a LEFT INVERSE of evaluation on code-values: `decodeV` reads
-- the `Ty` straight off the semantic value `eval ⌜c⌝` (a rigid
-- `vIn ∘ vInⁿ ∘ vPair` skeleton), and round-trips `El`. Then
-- `El c ≡ decodeV ⟦c⟧ ≡ decodeV ⟦d⟧ ≡ El d`, with `cong` doing the middle
-- step — no per-former discrimination.
--
-- Why the VALUE and not the reified `Term`: a decoder on the point-free
-- `Term` cannot be defined by pattern matching — a `terminal` (type `Unit`)
-- position sends Agda's coverage checker into the well-known `⟦F⟧F(μF) ≟ Unit`
-- stuck state (since `⟦One⟧F X = Unit`, `In` cannot be ruled out). `Val`'s
-- indices are plain `Ty`, so the decoder splits cleanly there. The one honest
-- gap this leaves: the checker's surface decision is `nf ⌜c⌝ ≡ nf ⌜d⌝` (reified
-- `Term`s); lifting THAT to the value equality below is `reifyVal`-injectivity
-- on code-values (true and structural — every constructor reifies to a
-- distinct `Term` head — but not proven here).
------------------------------------------------------------------------

-- The NbE value of a (closed) code — what `nf` reifies.
⟦_⟧v : Code → Val Unit U
⟦ c ⟧v = eval ⌜ c ⌝ vUnit

-- Left inverse: decode a code-VALUE back to the `Ty` it denotes.
-- (Total: non-code values fall through to `Void`; unreachable for `⟦_⟧v`.)
decodeV : Val Unit U → Ty
decodeV (vIn (vInl vUnit))                                    = Unit
decodeV (vIn (vInr (vInl vUnit)))                             = Nat
decodeV (vIn (vInr (vInr (vInl (vPair x y)))))               = decodeV x * decodeV y
decodeV (vIn (vInr (vInr (vInr (vInl (vPair x y))))))        = decodeV x ⇒ decodeV y
decodeV (vIn (vInr (vInr (vInr (vInr (vInl (vPair x y))))))) = decodeV x ⇒ decodeV y
decodeV (vIn (vInr (vInr (vInr (vInr (vInr (vPair x y))))))) = decodeV x * decodeV y
decodeV _                                                     = Void

-- Evaluation round-trips `El` — by induction on the code (6 cases).
decode-nfV : ∀ c → decodeV ⟦ c ⟧v ≡ El c
decode-nfV `unit    = refl
decode-nfV `nat     = refl
decode-nfV (a `× b) = cong₂ _*_ (decode-nfV a) (decode-nfV b)
decode-nfV (a `⇒ b) = cong₂ _⇒_ (decode-nfV a) (decode-nfV b)
decode-nfV (a `Π b) = cong₂ _⇒_ (decode-nfV a) (decode-nfV b)
decode-nfV (a `Σ b) = cong₂ _*_ (decode-nfV a) (decode-nfV b)

-- The weld: NbE-decided conversion (equal code-values) determines the decoded
-- type. `El` is therefore well-defined on conversion classes — a checker may
-- transport `El c` to `El d` whenever NbE identifies the codes.
El-weld : ∀ {c d} → ⟦ c ⟧v ≡ ⟦ d ⟧v → El c ≡ El d
El-weld {c} {d} p = trans (sym (decode-nfV c)) (trans (cong decodeV p) (decode-nfV d))

------------------------------------------------------------------------
-- Code-driven context extension + terms-of-type (the payoff the plan named).
------------------------------------------------------------------------

infixl 5 _▷ᶜ_
_▷ᶜ_ : Ctx → Code → Ctx
Γ ▷ᶜ A = Γ ▷ El A

-- A term of (decoded) type `A` in context `Γ`.
Tmᵗ : Ctx → Code → Set
Tmᵗ Γ A = Tm ⟦ Γ ⟧C (El A)

-- The context variable, as a genuine term of its type (second projection).
varᶜ : ∀ {Γ A} → Tmᵗ (Γ ▷ᶜ A) A
varᶜ = sndT

------------------------------------------------------------------------
-- Examples — each `refl` runs the decoder / a decision at type-check time.
------------------------------------------------------------------------

-- (1) Decoding the base and structural formers.
_ : El (`nat `⇒ `nat) ≡ (Nat ⇒ Nat)
_ = refl

_ : El (`nat `× `unit) ≡ (Nat * Unit)
_ = refl

-- (2) The honest ceiling, as a PROVEN equation: non-dependent Π decodes to
--     the arrow, Σ to the product — the correct meaning, and all a
--     first-order code can express.
_ : El (`nat `Π `nat) ≡ El (`nat `⇒ `nat)
_ = refl

_ : El (`nat `Σ `nat) ≡ El (`nat `× `nat)
_ = refl

-- (3) The reflection is a genuine `U`-code, decided convertible to itself by
--     the principled NbE (same `nf` as everywhere).
_ : nf ⌜ `nat `Π `nat ⌝ ≡ nf ⌜ `nat `Π `nat ⌝
_ = refl

-- (4) Code-driven context extension: the variable of a `Nat`-typed slot is a
--     real term of `Nat` in the extended context.
_ : Tmᵗ (∙ ▷ᶜ `nat) `nat
_ = varᶜ {∙} {`nat}

-- (5) …and of a compound (`Nat × Unit`)-typed slot. (`El` is not injective,
--     so the code `A` is passed explicitly rather than inferred through `El`.)
_ : Tmᵗ (∙ ▷ᶜ (`nat `× `unit)) (`nat `× `unit)
_ = varᶜ {∙} {`nat `× `unit}

------------------------------------------------------------------------
-- INDEXED FAMILIES — genuine term-dependency, WITHOUT induction-recursion.
--
-- A dependent type over an index type `I` is an OPEN code `Tm I U` — a
-- type-code with a free variable of type `I`. Its FIBRE at a closed index
-- `i : Tm Unit I` is `El`-of-`(F ⊙ i)`, read off the NbE value:
--
--   Fib F i = decodeV (eval (F ⊙ i) vUnit).
--
-- Because `eval (F ⊙ i) = eval F ∘ eval i`, the fibre depends on the index
-- ONLY through its NbE value — so convertible indices give EQUAL fibres
-- (`Fib-cong`). This is `Vec m ≅ Vec n` reduced to conversion on the index —
-- real dependency, decided by the principled NbE, with NO IR: the family is
-- an ordinary open code, not a code-valued function.
------------------------------------------------------------------------

Fam : Ty → Set
Fam I = Tm I U

Fib : ∀ {I} → Fam I → Tm Unit I → Ty
Fib F i = decodeV (eval (F ⊙ i) vUnit)

-- Conversion on the index (equal NbE values) ⇒ equal dependent-type fibres.
Fib-cong : ∀ {I} (F : Fam I) {i j : Tm Unit I}
         → eval i vUnit ≡ eval j vUnit → Fib F i ≡ Fib F j
Fib-cong F p = cong (λ v → decodeV (eval F v)) p

-- `Vec` OF `Nat` as a TYPE-LEVEL cata over the index: fold the `Nat` index
-- into a code — `0 ↦ unit`, `suc k ↦ nat × (Vec k)` — i.e. the n-fold product
-- `Natⁿ`. Genuine type-level computation landing in the universe.
VecNat : Fam (μ NatF)
VecNat = cataT NatF (case ⌜unit⌝ (⌜nat⌝ ×C idT))

-- Fibres computed by NbE (each `refl` runs the type-level fold + decoder):
_ : Fib VecNat zero ≡ Unit
_ = refl

_ : Fib VecNat one ≡ (El `nat * Unit)
_ = refl

_ : Fib VecNat two ≡ (El `nat * (El `nat * Unit))
_ = refl

-- THE DEPENDENCY DECIDED BY NbE: the index terms `double 1` and `2` differ
-- syntactically, but `double 1` COMPUTES to `2` under the type-level fold, so
-- the fibres are equal — `Vec (double 1) ≅ Vec 2`, decided by `refl`.
_ : Fib VecNat (double ⊙ one) ≡ Fib VecNat two
_ = refl
