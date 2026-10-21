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

module MAlonzo.Code.Once.Internal.Res where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool

-- Once.Internal.Res.Res
d_Res_8 a0 = ()
data T_Res_8 = C_stopped_12 | C_returns_14 AgdaAny
-- Once.Internal.Res.is-stopped
d_is'45'stopped_18 :: () -> T_Res_8 -> Bool
d_is'45'stopped_18 ~v0 v1 = du_is'45'stopped_18 v1
du_is'45'stopped_18 :: T_Res_8 -> Bool
du_is'45'stopped_18 v0
  = case coe v0 of
      C_stopped_12 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_returns_14 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Res.mapRes
d_mapRes_24 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_Res_8 -> T_Res_8
d_mapRes_24 ~v0 ~v1 v2 v3 = du_mapRes_24 v2 v3
du_mapRes_24 :: (AgdaAny -> AgdaAny) -> T_Res_8 -> T_Res_8
du_mapRes_24 v0 v1
  = case coe v1 of
      C_stopped_12 -> coe v1
      C_returns_14 v2 -> coe C_returns_14 (coe v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Res.Res-rel
d_Res'45'rel_38 a0 a1 a2 a3 a4 = ()
data T_Res'45'rel_38
  = C_rel'45'stopped_46 | C_rel'45'returns_52 AgdaAny
