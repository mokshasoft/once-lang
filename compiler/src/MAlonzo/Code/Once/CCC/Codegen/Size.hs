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

module MAlonzo.Code.Once.CCC.Codegen.Size where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.CCC.Codegen.Size.size
d_size_8 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Integer
d_size_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_Unit_16 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_Void_18 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C__'42'__20 v1 v2
        -> coe addInt (coe d_size_8 (coe v1)) (coe d_size_8 (coe v2))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v1 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe d_size_8 (coe v1))
                (coe d_size_8 (coe v2)))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v1 v2 v3
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IRTy.C_Int_30 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IRTy.C_Float_32 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.Size.size-words
d_size'45'words_32 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'words_32 = erased
