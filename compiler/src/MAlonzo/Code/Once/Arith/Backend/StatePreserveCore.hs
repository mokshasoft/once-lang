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

module MAlonzo.Code.Once.Arith.Backend.StatePreserveCore where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Once.Arith.Backend.StatePreserveCore.PreservesCCCState
d_PreservesCCCState_56 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                       a13
  = ()
data T_PreservesCCCState_56 = C_mkPresState_72 AgdaAny AgdaAny
-- Once.Arith.Backend.StatePreserveCore.PreservesCCCState.regs≈
d_regs'8776'_68 :: T_PreservesCCCState_56 -> AgdaAny
d_regs'8776'_68 v0
  = case coe v0 of
      C_mkPresState_72 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.StatePreserveCore.PreservesCCCState.mem≈
d_mem'8776'_70 :: T_PreservesCCCState_56 -> AgdaAny
d_mem'8776'_70 v0
  = case coe v0 of
      C_mkPresState_72 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.StatePreserveCore.preserves-state-refl
d_preserves'45'state'45'refl_78 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (Integer ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer -> AgdaAny -> T_PreservesCCCState_56
d_preserves'45'state'45'refl_78 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 v9
                                ~v10 v11 v12
  = du_preserves'45'state'45'refl_78 v3 v4 v6 v9 v11 v12
du_preserves'45'state'45'refl_78 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (Integer -> AgdaAny -> AgdaAny) ->
  Integer -> AgdaAny -> T_PreservesCCCState_56
du_preserves'45'state'45'refl_78 v0 v1 v2 v3 v4 v5
  = coe C_mkPresState_72 (coe v2 (coe v0 v5)) (coe v3 v4 (coe v1 v5))
-- Once.Arith.Backend.StatePreserveCore.preserves-state-trans
d_preserves'45'state'45'trans_92 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer -> AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (Integer ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T_PreservesCCCState_56 ->
  T_PreservesCCCState_56 -> T_PreservesCCCState_56
d_preserves'45'state'45'trans_92 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 ~v8
                                 ~v9 v10 v11 v12 v13 v14 v15 v16
  = du_preserves'45'state'45'trans_92
      v3 v4 v7 v10 v11 v12 v13 v14 v15 v16
du_preserves'45'state'45'trans_92 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Integer ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T_PreservesCCCState_56 ->
  T_PreservesCCCState_56 -> T_PreservesCCCState_56
du_preserves'45'state'45'trans_92 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      C_mkPresState_72 v10 v11
        -> case coe v9 of
             C_mkPresState_72 v12 v13
               -> coe
                    C_mkPresState_72
                    (coe v2 (coe v0 v5) (coe v0 v6) (coe v0 v7) v10 v12)
                    (coe v3 v4 (coe v1 v5) (coe v1 v6) (coe v1 v7) v11 v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
