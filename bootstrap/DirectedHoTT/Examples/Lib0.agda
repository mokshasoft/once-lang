-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- ⚠ GENERATED (PLAN-REF; scratch `canon.py`).
--
-- OCP-0009 · EXAMPLES — ONE instance of each parameterised module at the
-- EMPTY signature, shared by every example (PLAN-REF, D082).  Each
-- `open import M args` would be a NEW module application, and two of them
-- make a name ambiguous wherever they meet (a re-export, two imports);
-- opening the one instance here never does.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Lib0 where
open import DirectedHoTT.Spec.Syntax using ( ∅ᴷ )
open import DirectedHoTT.Examples.Sig0 using ( wf₀; ok₀; refs₀; tbl₀; tok₀ )

import DirectedHoTT.Lib.Amrec
import DirectedHoTT.Lib.AmrecClosed
import DirectedHoTT.Lib.AmrecInd
import DirectedHoTT.Lib.AmrecRen
import DirectedHoTT.Lib.Arith
import DirectedHoTT.Lib.ArithComm
import DirectedHoTT.Lib.ArithLe
import DirectedHoTT.Lib.ArithMonus
import DirectedHoTT.Lib.Dvd
import DirectedHoTT.Lib.DvdArith
import DirectedHoTT.Lib.IHCall
import DirectedHoTT.Lib.Max
import DirectedHoTT.Lib.MethAt
import DirectedHoTT.Lib.Monus
import DirectedHoTT.Lib.MonusLe
import DirectedHoTT.Lib.MonusPlus
import DirectedHoTT.Lib.Mul
import DirectedHoTT.Lib.Nat
import DirectedHoTT.Lib.NatCode
import DirectedHoTT.Lib.NatNum
import DirectedHoTT.Lib.NatVal
import DirectedHoTT.Lib.Natrec
import DirectedHoTT.Lib.Ord
import DirectedHoTT.Lib.Pair
import DirectedHoTT.Lib.Rec
import DirectedHoTT.Lib.Sorted
import DirectedHoTT.Lib.Strong
import DirectedHoTT.Lib.Sugar
import DirectedHoTT.Lib.Tel
import DirectedHoTT.Lib.TelAt
import DirectedHoTT.Lib.TelFold
import DirectedHoTT.Lib.TelFoldS
import DirectedHoTT.Lib.Wk
import DirectedHoTT.Metatheory.Canonicity
import DirectedHoTT.Metatheory.Fundamental.Syntactic
import DirectedHoTT.Metatheory.Premises
import DirectedHoTT.Metatheory.RedCong
import DirectedHoTT.Metatheory.SubjectReduction
import DirectedHoTT.Metatheory.SubjectReductionBase
import DirectedHoTT.Metatheory.TySub
import DirectedHoTT.Spec.Typing

module Inst where
  module Lib-Amrec = DirectedHoTT.Lib.Amrec ∅ᴷ 0
  module Lib-AmrecClosed = DirectedHoTT.Lib.AmrecClosed ∅ᴷ wf₀
  module Lib-AmrecInd = DirectedHoTT.Lib.AmrecInd ∅ᴷ 0
  module Lib-AmrecRen = DirectedHoTT.Lib.AmrecRen ∅ᴷ 0
  module Lib-Arith = DirectedHoTT.Lib.Arith ∅ᴷ 0
  module Lib-ArithComm = DirectedHoTT.Lib.ArithComm ∅ᴷ 0
  module Lib-ArithLe = DirectedHoTT.Lib.ArithLe ∅ᴷ 0
  module Lib-ArithMonus = DirectedHoTT.Lib.ArithMonus ∅ᴷ 0
  module Lib-Dvd = DirectedHoTT.Lib.Dvd ∅ᴷ 0
  module Lib-DvdArith = DirectedHoTT.Lib.DvdArith ∅ᴷ 0
  module Lib-IHCall = DirectedHoTT.Lib.IHCall ∅ᴷ 0
  module Lib-Max = DirectedHoTT.Lib.Max ∅ᴷ 0
  module Lib-MethAt = DirectedHoTT.Lib.MethAt ∅ᴷ 0 ok₀
  module Lib-Monus = DirectedHoTT.Lib.Monus ∅ᴷ 0
  module Lib-MonusLe = DirectedHoTT.Lib.MonusLe ∅ᴷ 0
  module Lib-MonusPlus = DirectedHoTT.Lib.MonusPlus ∅ᴷ 0
  module Lib-Mul = DirectedHoTT.Lib.Mul ∅ᴷ 0
  module Lib-Nat = DirectedHoTT.Lib.Nat ∅ᴷ 0
  module Lib-NatCode = DirectedHoTT.Lib.NatCode ∅ᴷ 0
  module Lib-NatNum = DirectedHoTT.Lib.NatNum ∅ᴷ 0
  module Lib-NatVal = DirectedHoTT.Lib.NatVal ∅ᴷ
  module Lib-Natrec = DirectedHoTT.Lib.Natrec ∅ᴷ 0
  module Lib-Ord = DirectedHoTT.Lib.Ord ∅ᴷ 0
  module Lib-Pair = DirectedHoTT.Lib.Pair ∅ᴷ 0
  module Lib-Rec = DirectedHoTT.Lib.Rec ∅ᴷ 0
  module Lib-Sorted = DirectedHoTT.Lib.Sorted ∅ᴷ 0 ok₀
  module Lib-Strong = DirectedHoTT.Lib.Strong ∅ᴷ 0
  module Lib-Sugar = DirectedHoTT.Lib.Sugar ∅ᴷ 0 ok₀
  module Lib-Tel = DirectedHoTT.Lib.Tel ∅ᴷ 0 ok₀
  module Lib-TelAt = DirectedHoTT.Lib.TelAt ∅ᴷ 0 ok₀
  module Lib-TelFold = DirectedHoTT.Lib.TelFold ∅ᴷ 0 ok₀
  module Lib-TelFoldS = DirectedHoTT.Lib.TelFoldS ∅ᴷ 0 ok₀
  module Lib-Wk = DirectedHoTT.Lib.Wk ∅ᴷ 0
  module Metatheory-Canonicity = DirectedHoTT.Metatheory.Canonicity ∅ᴷ wf₀
  module Metatheory-Fundamental-Syntactic = DirectedHoTT.Metatheory.Fundamental.Syntactic ∅ᴷ
  module Metatheory-Premises = DirectedHoTT.Metatheory.Premises ∅ᴷ 0
  module Metatheory-RedCong = DirectedHoTT.Metatheory.RedCong ∅ᴷ
  module Metatheory-SubjectReduction = DirectedHoTT.Metatheory.SubjectReduction ∅ᴷ 0 ok₀
  module Metatheory-SubjectReductionBase = DirectedHoTT.Metatheory.SubjectReductionBase ∅ᴷ
  module Metatheory-TySub = DirectedHoTT.Metatheory.TySub ∅ᴷ 0
  module Spec-Typing = DirectedHoTT.Spec.Typing ∅ᴷ 0
open Inst public
