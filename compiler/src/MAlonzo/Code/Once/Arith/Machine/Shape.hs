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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Once.Arith.Type

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
-- Once.Arith.Machine.Shape.Path
d_Path_68 a0 a1 = ()
data T_Path_68
  = C_here'45'int_70 | C_here'45'flt_72 | C_go'45'fst_80 T_Path_68 |
    C_go'45'snd_88 T_Path_68
-- Once.Arith.Machine.Shape.LeafVal
d_LeafVal_90 :: MAlonzo.Code.Once.Arith.Type.T_NumType_6 -> ()
d_LeafVal_90 = erased
-- Once.Arith.Machine.Shape.readLeaf
d_readLeaf_96 ::
  T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  T_Path_68 -> AgdaAny -> AgdaAny
d_readLeaf_96 v0 ~v1 v2 v3 = du_readLeaf_96 v0 v2 v3
du_readLeaf_96 :: T_InputShape_8 -> T_Path_68 -> AgdaAny -> AgdaAny
du_readLeaf_96 v0 v1 v2
  = case coe v1 of
      C_here'45'int_70 -> coe v2
      C_here'45'flt_72 -> coe v2
      C_go'45'fst_80 v6
        -> case coe v0 of
             C_shape'45'pair_16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe du_readLeaf_96 (coe v7) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_go'45'snd_88 v6
        -> case coe v0 of
             C_shape'45'pair_16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe du_readLeaf_96 (coe v8) (coe v6) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Shape.⌊_⌋ᴾ
d_'8970'_'8971''7486'_114 ::
  T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  T_Path_68 -> [T_Side_24]
d_'8970'_'8971''7486'_114 v0 ~v1 v2
  = du_'8970'_'8971''7486'_114 v0 v2
du_'8970'_'8971''7486'_114 ::
  T_InputShape_8 -> T_Path_68 -> [T_Side_24]
du_'8970'_'8971''7486'_114 v0 v1
  = case coe v1 of
      C_here'45'int_70
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_here'45'flt_72
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_go'45'fst_80 v5
        -> case coe v0 of
             C_shape'45'pair_16 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_Fst_26)
                    (coe du_'8970'_'8971''7486'_114 (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_go'45'snd_88 v5
        -> case coe v0 of
             C_shape'45'pair_16 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe C_Snd_28)
                    (coe du_'8970'_'8971''7486'_114 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Machine.Shape.project-path
d_project'45'path_126 ::
  T_InputShape_8 ->
  T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_project'45'path_126 = erased
-- Once.Arith.Machine.Shape.projectF-path
d_projectF'45'path_144 ::
  T_InputShape_8 ->
  T_Path_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_projectF'45'path_144 = erased
-- Once.Arith.Machine.Shape.typePath?
d_typePath'63'_160 ::
  T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  [T_Side_24] -> Maybe T_Path_68
d_typePath'63'_160 v0 v1 v2
  = case coe v0 of
      C_shape'45'unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_shape'45'int_12
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> case coe v2 of
                    []
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_here'45'int_70)
                    (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C_shape'45'float_14
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> case coe v2 of
                    []
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_here'45'flt_72)
                    (:) v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_shape'45'pair_16 v3 v4
        -> case coe v2 of
             [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             (:) v5 v6
               -> case coe v5 of
                    C_Fst_26
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe C_go'45'fst_80)
                           (d_typePath'63'_160 (coe v3) (coe v1) (coe v6))
                    C_Snd_28
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe C_go'45'snd_88)
                           (d_typePath'63'_160 (coe v4) (coe v1) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
