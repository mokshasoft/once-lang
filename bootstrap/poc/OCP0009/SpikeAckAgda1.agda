------------------------------------------------------------------------
-- OCP-0009 — ACKERMANN IN PURE AGDA, cost control #1: FOR FREE.
--
-- Nothing to do with the kernel.  Written the obvious way, and Agda's own
-- termination checker accepts it — because that checker ALREADY does
-- lexicographic descent on the argument tuple, which is exactly the
-- power `⊢lexrec` exists to give the object language.
--
-- So this is the "what does it cost when the ambient system just has the
-- feature" baseline.  Self-contained: no imports, so the number is the
-- proof and nothing else.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeAckAgda1 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- ★ NO `Acc`, NO measure, NO `TERMINATING`.  The descent is on the PAIR
--   (m, n): the first call drops m; the inner call holds m and drops n;
--   the outer call drops m.  Agda's termination checker sees it.
ack : ℕ → ℕ → ℕ
ack zero    n       = suc n
ack (suc m) zero    = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)
