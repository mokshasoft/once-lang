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

module MAlonzo.Code.Once.CCC.Codegen.FlatLayout where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.Size
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.CCC.Codegen.FlatLayout.Kind
d_Kind_8 = ()
data T_Kind_8 = C_word_10 | C_flat_12
-- Once.CCC.Codegen.FlatLayout.kind
d_kind_14 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_Kind_8
d_kind_14 v0
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_Unit_16 -> coe C_flat_12
      MAlonzo.Code.Once.IRTy.C_Void_18 -> coe C_flat_12
      MAlonzo.Code.Once.IRTy.C__'42'__20 v1 v2 -> coe C_flat_12
      MAlonzo.Code.Once.IRTy.C__'43'__22 v1 v2 -> coe C_flat_12
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v1 v2 v3
        -> coe C_word_10
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v1 -> coe C_word_10
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v1 -> coe C_word_10
      MAlonzo.Code.Once.IRTy.C_Int_30 -> coe C_word_10
      MAlonzo.Code.Once.IRTy.C_Float_32 -> coe C_word_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.copy-from
d_copy'45'from_26 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_copy'45'from_26 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v5 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                   (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244 (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                         (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                            (coe addInt (coe v2) (coe v3)))
                         (coe
                            d_copy'45'from_26 (coe v0) (coe v1) (coe v2)
                            (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v5))))))
-- Once.CCC.Codegen.FlatLayout.fill
d_fill_50 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_fill_50 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246 (coe v0))
                   (coe
                      d_fill_50 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))))
-- Once.CCC.Codegen.FlatLayout.put-k
d_put'45'k_64 ::
  T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_put'45'k_64 v0 v1 v2 v3 v4
  = case coe v0 of
      C_word_10
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                   (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246 (coe v4))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      C_flat_12
        -> coe
             d_copy'45'from_26 (coe v2) (coe v3) (coe v4) (coe (0 :: Integer))
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.put
d_put_86 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_put_86 v0
  = coe
      d_put'45'k_64 (coe d_kind_14 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0))
-- Once.CCC.Codegen.FlatLayout.get-k
d_get'45'k_90 ::
  T_Kind_8 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_get'45'k_90 v0 v1 v2
  = case coe v0 of
      C_word_10
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      C_flat_12
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2248 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.get-ik
d_get'45'ik_98 ::
  T_Kind_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174
d_get'45'ik_98 v0 v1 v2
  = case coe v0 of
      C_word_10
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244 (coe v2)
      C_flat_12
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176
             _ -> coe
                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2248 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.get-i
d_get'45'i_106 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174
d_get'45'i_106 v0
  = coe
      d_get'45'ik_98 (coe d_kind_14 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0))
-- Once.CCC.Codegen.FlatLayout.get-k-one
d_get'45'k'45'one_116 ::
  T_Kind_8 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_get'45'k'45'one_116 = erased
-- Once.CCC.Codegen.FlatLayout.get
d_get_124 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_get_124 v0
  = coe
      d_get'45'k_90 (coe d_kind_14 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0))
-- Once.CCC.Codegen.FlatLayout.get-one
d_get'45'one_132 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_get'45'one_132 = erased
-- Once.CCC.Codegen.FlatLayout._.copy-from-All
d_copy'45'from'45'All_156 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_copy'45'from'45'All_156 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_copy'45'from'45'All_156 v3 v4 v5 v6 v7 v8 v9
du_copy'45'from'45'All_156 ::
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_copy'45'from'45'All_156 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      0 -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> let v7 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v3
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 (coe v5 v1)
                   (coe
                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                      (coe
                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                         (coe v6 (addInt (coe v0) (coe v1)))
                         (coe
                            du_copy'45'from'45'All_156 (coe v0)
                            (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v7) (coe v3)
                            (coe v4) (coe v5) (coe v6))))))
-- Once.CCC.Codegen.FlatLayout._.put-k-All
d_put'45'k'45'All_206 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_put'45'k'45'All_206 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_put'45'k'45'All_206 v1 v2 v5 v6 v7 v8 v9 v10
du_put'45'k'45'All_206 ::
  T_Kind_8 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_put'45'k'45'All_206 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v0 of
      C_word_10
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 (coe v7 v2)
                   (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
      C_flat_12
        -> coe
             du_copy'45'from'45'All_156 (coe v2) (coe (0 :: Integer)) (coe v1)
             (coe v3) (coe v4) (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout._.put-All
d_put'45'All_256 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_put'45'All_256 ~v0 v1 = du_put'45'All_256 v1
du_put'45'All_256 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_put'45'All_256 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_put'45'k'45'All_206 (coe d_kind_14 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0)) v3 v4 v5
      v6 v7 v8
-- Once.CCC.Codegen.FlatLayout._.get-k-All
d_get'45'k'45'All_270 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  T_Kind_8 ->
  Integer ->
  Integer ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_get'45'k'45'All_270 ~v0 v1 v2 v3 v4 v5 v6
  = du_get'45'k'45'All_270 v1 v2 v3 v4 v5 v6
du_get'45'k'45'All_270 ::
  T_Kind_8 ->
  Integer ->
  Integer ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_get'45'k'45'All_270 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      C_word_10
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 (coe v3 v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      C_flat_12
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             _ -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 (coe v4 v2)
                    (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout._.get-All
d_get'45'All_306 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_get'45'All_306 ~v0 v1 = du_get'45'All_306 v1
du_get'45'All_306 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer -> AgdaAny) ->
  (Integer -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_get'45'All_306 v0
  = coe
      du_get'45'k'45'All_270 (coe d_kind_14 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0))
-- Once.CCC.Codegen.FlatLayout._.get-ik-P
d_get'45'ik'45'P_320 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  T_Kind_8 ->
  Integer ->
  Integer ->
  (Integer -> AgdaAny) -> (Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_get'45'ik'45'P_320 ~v0 v1 v2 v3 v4 v5 v6
  = du_get'45'ik'45'P_320 v1 v2 v3 v4 v5 v6
du_get'45'ik'45'P_320 ::
  T_Kind_8 ->
  Integer ->
  Integer ->
  (Integer -> AgdaAny) -> (Integer -> AgdaAny) -> AgdaAny -> AgdaAny
du_get'45'ik'45'P_320 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      C_word_10 -> coe v3 v2
      C_flat_12
        -> case coe v1 of
             0 -> coe v5
             _ -> coe v4 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout._.get-i-P
d_get'45'i'45'P_356 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer -> AgdaAny) -> (Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_get'45'i'45'P_356 ~v0 v1 = du_get'45'i'45'P_356 v1
du_get'45'i'45'P_356 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer -> AgdaAny) -> (Integer -> AgdaAny) -> AgdaAny -> AgdaAny
du_get'45'i'45'P_356 v0
  = coe
      du_get'45'ik'45'P_320 (coe d_kind_14 (coe v0))
      (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0))
-- Once.CCC.Codegen.FlatLayout._.fill-All
d_fill'45'All_366 ::
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
   ()) ->
  Integer ->
  Integer ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fill'45'All_366 ~v0 v1 v2 v3 v4 = du_fill'45'All_366 v1 v2 v3 v4
du_fill'45'All_366 ::
  Integer ->
  Integer ->
  AgdaAny ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fill'45'All_366 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v2
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 (coe v3 v0)
                   (coe
                      du_fill'45'All_366 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe v4) (coe v2) (coe v3))))
-- Once.CCC.Codegen.FlatLayout.ssize
d_ssize_384 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
d_ssize_384 ~v0 v1 = du_ssize_384 v1
du_ssize_384 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Integer
du_ssize_384 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             addInt (coe du_ssize_384 (coe v1)) (coe du_ssize_384 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                (coe du_ssize_384 (coe v1)) (coe du_ssize_384 (coe v2)))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.skind
d_skind_396 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_Kind_8
d_skind_396 ~v0 v1 = du_skind_396 v1
du_skind_396 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_Kind_8
du_skind_396 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1 -> coe C_word_10
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_flat_12
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_flat_12
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2 -> coe C_flat_12
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2 -> coe C_flat_12
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe C_word_10
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1 -> coe C_word_10
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2 -> coe C_word_10
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_word_10
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe C_word_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.lkind
d_lkind_398 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_Kind_8 -> T_Kind_8
d_lkind_398 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2 -> coe du_skind_396 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3 -> coe C_flat_12
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3 -> coe C_flat_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.lsz
d_lsz_410 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer -> Integer
d_lsz_410 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2 -> coe du_ssize_384 (coe v2)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                (coe d_lsz_410 (coe v2) (coe v1))
                (coe d_lsz_410 (coe v3) (coe v1)))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> coe
             addInt (coe d_lsz_410 (coe v2) (coe v1))
             (coe d_lsz_410 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.FlatLayout.size-ssize
d_size'45'ssize_432 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_size'45'ssize_432 = erased
-- Once.CCC.Codegen.FlatLayout.kind-skind
d_kind'45'skind_452 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_kind'45'skind_452 = erased
