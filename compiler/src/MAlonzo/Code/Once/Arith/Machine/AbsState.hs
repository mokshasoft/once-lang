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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Arith.Machine.AbsState.InputShape
d_InputShape_8 = ()
data T_InputShape_8
  = C_shape'45'unit_10 | C_shape'45'int_12 |
    C_shape'45'pair_14 T_InputShape_8 T_InputShape_8
-- Once.Arith.Machine.AbsState.⟦_⟧S
d_'10214'_'10215'S_16 :: T_InputShape_8 -> ()
d_'10214'_'10215'S_16 = erased
-- Once.Arith.Machine.AbsState.Side
d_Side_22 = ()
data T_Side_22 = C_Fst_24 | C_Snd_26
-- Once.Arith.Machine.AbsState.InputPath
d_InputPath_28 :: ()
d_InputPath_28 = erased
-- Once.Arith.Machine.AbsState.project
d_project_32 ::
  T_InputShape_8 -> [T_Side_22] -> AgdaAny -> Maybe Integer
d_project_32 v0 v1 v2
  = case coe v0 of
      C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_shape'45'int_12
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_shape'45'pair_14 v3 v4
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    C_Fst_24
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_project_32 (coe v3) (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_Snd_26
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_project_32 (coe v4) (coe v6) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.NumValue
d_NumValue_48 :: ()
d_NumValue_48 = erased
-- Once.Arith.Machine.AbsState.Store
d_Store_50 :: ()
d_Store_50 = erased
-- Once.Arith.Machine.AbsState.empty-store
d_empty'45'store_52 :: Integer -> Maybe Integer
d_empty'45'store_52 ~v0 = du_empty'45'store_52
du_empty'45'store_52 :: Maybe Integer
du_empty'45'store_52
  = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Machine.AbsState._[_↦_]
d__'91'_'8614'_'93'_54 ::
  (Integer -> Maybe Integer) ->
  Integer -> Maybe Integer -> Integer -> Maybe Integer
d__'91'_'8614'_'93'_54 v0 v1 v2 v3
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
d__'91'_'93'_84 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d__'91'_'93'_84 v0 v1 = coe v0 v1
-- Once.Arith.Machine.AbsState.store-write-same
d_store'45'write'45'same_96 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'write'45'same_96 = erased
-- Once.Arith.Machine.AbsState.store-write-other
d_store'45'write'45'other_130 ::
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Maybe Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'write'45'other_130 = erased
-- Once.Arith.Machine.AbsState.ArithAbsState
d_ArithAbsState_170 a0 = ()
data T_ArithAbsState_170
  = C_mk'45'state_190 (Integer -> Maybe Integer)
                      (Integer -> Maybe Integer) (Maybe Integer) AgdaAny
-- Once.Arith.Machine.AbsState.ArithAbsState.regs
d_regs_182 :: T_ArithAbsState_170 -> Integer -> Maybe Integer
d_regs_182 v0
  = case coe v0 of
      C_mk'45'state_190 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.ArithAbsState.scratch
d_scratch_184 :: T_ArithAbsState_170 -> Integer -> Maybe Integer
d_scratch_184 v0
  = case coe v0 of
      C_mk'45'state_190 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.ArithAbsState.output
d_output_186 :: T_ArithAbsState_170 -> Maybe Integer
d_output_186 v0
  = case coe v0 of
      C_mk'45'state_190 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.ArithAbsState.input
d_input_188 :: T_ArithAbsState_170 -> AgdaAny
d_input_188 v0
  = case coe v0 of
      C_mk'45'state_190 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.AbsState.init
d_init_194 :: T_InputShape_8 -> AgdaAny -> T_ArithAbsState_170
d_init_194 ~v0 v1 = du_init_194 v1
du_init_194 :: AgdaAny -> T_ArithAbsState_170
du_init_194 v0
  = coe
      C_mk'45'state_190 (\ v1 -> coe du_empty'45'store_52)
      (\ v1 -> coe du_empty'45'store_52)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v0)
-- Once.Arith.Machine.AbsState.output-of
d_output'45'of_200 :: T_ArithAbsState_170 -> Maybe Integer
d_output'45'of_200 v0 = coe d_output_186 (coe v0)
