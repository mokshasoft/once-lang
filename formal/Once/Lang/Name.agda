{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Name — the dotted form of a canonical name (`Once.Spec.Name`),
-- used as an external operation's key.
------------------------------------------------------------------------

module Once.Lang.Name where

open import Data.List using ([]; _∷_)
open import Data.String using (String)
import Data.String as String
open import Once.Spec.Name using (CanonicalName; canonical)

showCanonical : CanonicalName → String
showCanonical (canonical [])        = ""
showCanonical (canonical (x ∷ []))  = x
{-# CATCHALL #-}
showCanonical (canonical (x ∷ xs))  = x String.++ "." String.++ showCanonical (canonical xs)
