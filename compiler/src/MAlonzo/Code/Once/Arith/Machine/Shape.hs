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

module MAlonzo.Code.Once.Arith.Machine.Shape where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma

-- Once.Arith.Machine.Shape.InputShape
d_InputShape_8 = ()
data T_InputShape_8
  = C_shape'45'unit_10 | C_shape'45'int_12 | C_shape'45'float_14 |
    C_shape'45'pair_16 T_InputShape_8 T_InputShape_8
-- Once.Arith.Machine.Shape.⟦_⟧S
d_'10214'_'10215'S_18 :: T_InputShape_8 -> ()
d_'10214'_'10215'S_18 = erased
-- Once.Arith.Machine.Shape.Side
d_Side_24 = ()
data T_Side_24 = C_Fst_26 | C_Snd_28
-- Once.Arith.Machine.Shape.InputPath
d_InputPath_30 :: ()
d_InputPath_30 = erased
-- Once.Arith.Machine.Shape.project
d_project_34 ::
  T_InputShape_8 -> [T_Side_24] -> AgdaAny -> Maybe Integer
d_project_34 v0 v1 v2
  = case coe v0 of
      C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_shape'45'int_12
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_shape'45'float_14
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_shape'45'pair_16 v3 v4
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    C_Fst_26
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_project_34 (coe v3) (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_Snd_28
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_project_34 (coe v4) (coe v6) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Shape.projectF
d_projectF_52 ::
  T_InputShape_8 -> [T_Side_24] -> AgdaAny -> Maybe Integer
d_projectF_52 v0 v1 v2
  = case coe v0 of
      C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_shape'45'int_12
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_shape'45'float_14
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_shape'45'pair_16 v3 v4
        -> case coe v1 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    C_Fst_26
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectF_52 (coe v3) (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_Snd_28
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe d_projectF_52 (coe v4) (coe v6) (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
