------------------------------------------------------------------------
-- OCP-0009 · The SUMMIT in miniature — verified COMPILER CORRECTNESS in-theory
--
-- The whole OCP is motivated by one goal: state and prove properties of Once
-- programs — up to COMPILER CORRECTNESS — inside the language itself. With the
-- dependent-type stack now in place (indexed families for relations/data,
-- structural induction as the eliminator), this module exhibits the SHAPE of
-- that summit on the canonical example: a tiny expression language, a direct
-- evaluator, a compiler to a stack machine, and a machine-checked theorem
--
--   compile-correct : ∀ e s → exec (compile e) s ≡ eval e ∷ s
--
-- i.e. the compiled code, run on the stack machine, computes exactly the
-- evaluator's answer. Proved by STRUCTURAL INDUCTION on the expression (the
-- `Cata` shape), with one lemma (`exec` distributes over code concatenation).
--
-- This is the honest shape of Rung 6: you CAN prove the compiler correct for
-- REPRESENTED programs (a structural induction over a given `e`); what you
-- cannot do is a total self-interpreter (the fuel-bounded diagonalization
-- ceiling). This is exactly what the real Once compiler proves in the large
-- (`Once.Adequacy.*` on `origin/ocp-0006-once-spec`) — here in one file.
------------------------------------------------------------------------

module poc.OCP0009.NbEPSummit where

open import normalizer.Syntax.Types using ( _≡_; refl; cong; trans )

------------------------------------------------------------------------
-- Prelude: naturals with addition, and lists.
------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

------------------------------------------------------------------------
-- Source language and its direct evaluator (the SPEC).
------------------------------------------------------------------------

data Expr : Set where
  lit : ℕ → Expr
  add : Expr → Expr → Expr

eval : Expr → ℕ
eval (lit n)   = n
eval (add a b) = eval a + eval b

------------------------------------------------------------------------
-- Target: a stack machine (the IMPLEMENTATION).
------------------------------------------------------------------------

data Instr : Set where
  push : ℕ → Instr
  plus : Instr

Code  = List Instr
Stack = List ℕ

-- Execution. The `plus` short-stack cases "skip and continue" (never reached by
-- compiled code, but chosen so `exec` distributes cleanly over `_++_`).
exec : Code → Stack → Stack
exec []           s           = s
exec (push n ∷ c) s           = exec c (n ∷ s)
exec (plus ∷ c)   (b ∷ a ∷ s) = exec c ((a + b) ∷ s)
exec (plus ∷ c)   (a ∷ [])    = exec c (a ∷ [])
exec (plus ∷ c)   []          = exec c []

------------------------------------------------------------------------
-- The compiler.
------------------------------------------------------------------------

compile : Expr → Code
compile (lit n)   = push n ∷ []
compile (add a b) = compile a ++ (compile b ++ (plus ∷ []))

------------------------------------------------------------------------
-- The correctness proof.
------------------------------------------------------------------------

-- Lemma: `exec` distributes over code concatenation (by induction on the code).
exec-++ : ∀ (c d : Code) (s : Stack) → exec (c ++ d) s ≡ exec d (exec c s)
exec-++ []           d s           = refl
exec-++ (push n ∷ c) d s           = exec-++ c d (n ∷ s)
exec-++ (plus ∷ c)   d (b ∷ a ∷ s) = exec-++ c d ((a + b) ∷ s)
exec-++ (plus ∷ c)   d (a ∷ [])    = exec-++ c d (a ∷ [])
exec-++ (plus ∷ c)   d []          = exec-++ c d []

-- The theorem: compiled code computes the evaluator's answer, pushed on the
-- stack. By structural induction on the expression.
compile-correct : ∀ (e : Expr) (s : Stack) → exec (compile e) s ≡ (eval e ∷ s)
compile-correct (lit n)   s = refl
compile-correct (add a b) s =
  trans (exec-++ (compile a) (compile b ++ (plus ∷ [])) s)
  (trans (cong (exec (compile b ++ (plus ∷ []))) (compile-correct a s))
  (trans (exec-++ (compile b) (plus ∷ []) (eval a ∷ s))
         (cong (exec (plus ∷ [])) (compile-correct b (eval a ∷ s)))))

------------------------------------------------------------------------
-- A concrete run — `(1 + 2) + 4` compiles-and-runs to `7`, on the nose.
------------------------------------------------------------------------

one two four : ℕ
one  = suc zero
two  = suc one
four = suc (suc two)

prog : Expr
prog = add (add (lit one) (lit two)) (lit four)

emptyStack : Stack
emptyStack = []

_ : exec (compile prog) emptyStack ≡ (eval prog ∷ emptyStack)
_ = compile-correct prog emptyStack
