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

module MAlonzo.Code.Once.Arith.Machine.AbsState where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Machine.AbsState.NumValue
d_NumValue_8 :: ()
d_NumValue_8 = erased
-- Once.Arith.Machine.AbsState.Store
d_Store_10 :: ()
d_Store_10 = erased
-- Once.Arith.Machine.AbsState.empty-store
d_empty'45'store_12 :: Integer -> Maybe Integer
d_empty'45'store_12 ~v0 = du_empty'45'store_12
du_empty'45'store_12 :: Maybe Integer
du_empty'45'store_12
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.AbsState._[_↦_]
d__'91'_'8614'_'93'_14 ::
  (Integer -> Maybe Integer) ->
  Integer -> Maybe Integer -> Integer -> Maybe Integer
d__'91'_'8614'_'93'_14 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v4 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe v1))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe eqInt (coe v1) (coe v3))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe seq (coe v6) (coe v2)
                else coe seq (coe v6) (coe v0 v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Arith.Machine.AbsState._[_]
d__'91'_'93'_44 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d__'91'_'93'_44 v0 v1 = coe v0 v1
-- Once.Arith.Machine.AbsState.store-write-same
d_store'45'write'45'same_56 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'write'45'same_56 = erased
-- Once.Arith.Machine.AbsState.store-write-other
d_store'45'write'45'other_90 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Maybe Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'write'45'other_90 = erased
-- Once.Arith.Machine.AbsState.ArithAbsState
d_ArithAbsState_130 a0 = ()
data T_ArithAbsState_130
  = C_mk'45'state_150 (Integer -> Maybe Integer)
                      (Integer -> Maybe Integer) (Maybe Integer) AgdaAny
-- Once.Arith.Machine.AbsState.ArithAbsState.regs
d_regs_142 :: T_ArithAbsState_130 -> Integer -> Maybe Integer
d_regs_142 v0
  = case coe v0 of
      C_mk'45'state_150 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.ArithAbsState.scratch
d_scratch_144 :: T_ArithAbsState_130 -> Integer -> Maybe Integer
d_scratch_144 v0
  = case coe v0 of
      C_mk'45'state_150 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.ArithAbsState.output
d_output_146 :: T_ArithAbsState_130 -> Maybe Integer
d_output_146 v0
  = case coe v0 of
      C_mk'45'state_150 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.ArithAbsState.input
d_input_148 :: T_ArithAbsState_130 -> AgdaAny
d_input_148 v0
  = case coe v0 of
      C_mk'45'state_150 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.init
d_init_154 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  AgdaAny -> T_ArithAbsState_130
d_init_154 ~v0 v1 = du_init_154 v1
du_init_154 :: AgdaAny -> T_ArithAbsState_130
du_init_154 v0
  = coe
      C_mk'45'state_150 (\ v1 -> coe du_empty'45'store_12)
      (\ v1 -> coe du_empty'45'store_12)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v0)
-- Once.Arith.Machine.AbsState.output-of
d_output'45'of_160 :: T_ArithAbsState_130 -> Maybe Integer
d_output'45'of_160 v0 = coe d_output_146 (coe v0)
