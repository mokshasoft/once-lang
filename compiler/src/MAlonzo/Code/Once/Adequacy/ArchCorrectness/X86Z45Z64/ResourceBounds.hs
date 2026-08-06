{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.ResourceBounds where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CanonicalName

-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.HeapRoom
d_HeapRoom_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_HeapRoom_12 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.StackRoom
d_StackRoom_24 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_StackRoom_24 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.ResourceBounds.CallRoom
d_CallRoom_38 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> ()
d_CallRoom_38 = erased
