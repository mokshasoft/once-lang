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

module MAlonzo.Code.Once.Spec.Name where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String

-- Once.Spec.Name.CanonicalName
d_CanonicalName_6 = ()
newtype T_CanonicalName_6
  = C_canonical_12 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.Spec.Name.CanonicalName.parts
d_parts_10 ::
  T_CanonicalName_6 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_parts_10 v0
  = case coe v0 of
      C_canonical_12 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Name.bare
d_bare_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CanonicalName_6
d_bare_14 v0
  = coe
      C_canonical_12
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
