-- SPIKE negative control for GenSynQuoteFrag: must FAIL on conversion
-- (the variable and the λ swap their tags).
{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl )
open import DirectedHoTT.Spec.Syntax using ( ε; vz )
import DirectedHoTT.Spec.Syntax as S
open import tmp.GenSyn
open import tmp.GenSynFrag
open import tmp.GenSynQuote
open import tmp.GenSynQuoteFrag using ( EK; qTm )
module tmp.GenSynQuoteNeg where
open Quote EK
bad : qTm (lam (var vz)) ≡ conₗ 0 (S.pair (conₗ 1 (S.pair S.fzero S.unit)) S.unit)
bad = refl
