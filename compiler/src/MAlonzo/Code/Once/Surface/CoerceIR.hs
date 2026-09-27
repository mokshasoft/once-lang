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

module MAlonzo.Code.Once.Surface.CoerceIR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Surface.CoerceIR.wrapArr
d_wrapArr_14 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_wrapArr_14 v0 v1 v2 ~v3 v4 v5 = du_wrapArr_14 v0 v1 v2 v4 v5
du_wrapArr_14 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_wrapArr_14 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
               (coe v0))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28 v1 v3
                  (coe MAlonzo.Code.Once.IR.C_snd_48)))))
-- Once.Surface.CoerceIR.wrapArr₀
d_wrapArr'8320'_24 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_wrapArr'8320'_24 v0 ~v1 v2 = du_wrapArr'8320'_24 v0 v2
du_wrapArr'8320'_24 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_wrapArr'8320'_24 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1
         (coe MAlonzo.Code.Once.IR.C_apply_90))
-- Once.Surface.CoerceIR.coeIR
d_coeIR_32 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_coeIR_32 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
        -> coe MAlonzo.Code.Once.IR.C_initial_76
      MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v10 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         du_wrapArr'8320'_24
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15))
                                         (coe d_coeIR_32 (coe v15) (coe v20) (coe v11))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         du_wrapArr_14
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v13))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v18))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15))
                                         (coe d_coeIR_32 (coe v18) (coe v13) (coe v10))
                                         (coe d_coeIR_32 (coe v15) (coe v20) (coe v11))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         du_wrapArr_14
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v13))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v18))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15))
                                         (coe d_coeIR_32 (coe v18) (coe v13) (coe v10))
                                         (coe d_coeIR_32 (coe v15) (coe v20) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9))
                              (d_coeIR_32 (coe v9) (coe v11) (coe v7))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10))
                              (d_coeIR_32 (coe v10) (coe v12) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_snd_48))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> coe
                           MAlonzo.Code.Once.IR.C_case_68
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v11))
                              (coe MAlonzo.Code.Once.IR.C_inl_54)
                              (d_coeIR_32 (coe v9) (coe v11) (coe v7)))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                              (coe MAlonzo.Code.Once.IR.C_inr_60)
                              (d_coeIR_32 (coe v10) (coe v12) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v6
        -> coe MAlonzo.Code.Once.IR.C_id_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.VoidFree
d_VoidFree_58 a0 a1 a2 = ()
data T_VoidFree_58
  = C_vf'45'void_60 | C_vf'45'unit_62 | C_vf'45'int_64 |
    C_vf'45'float_66 | C_vf'45'str_68 | C_vf'45'buffer_70 |
    C_vf'45'arr_92 T_VoidFree_58 T_VoidFree_58 |
    C_vf'45'prod_106 T_VoidFree_58 T_VoidFree_58 |
    C_vf'45'sum_120 T_VoidFree_58 T_VoidFree_58 | C_vf'45'μ_124 |
    C_vf'45'ν_134
-- Once.Surface.CoerceIR.two
d_two_142 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_two_142 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 = du_two_142 v3 v6 v7
du_two_142 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_two_142 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                      -> case coe v2 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                             -> if coe v6
                                  then case coe v7 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                           -> coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                   (coe v0 v5 v8))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  else coe
                                         seq (coe v7)
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                            (coe v6)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v3)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.arr-a
d_arr'45'a_194 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  T_VoidFree_58 -> T_VoidFree_58
d_arr'45'a_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_arr'45'a_194 v10
du_arr'45'a_194 :: T_VoidFree_58 -> T_VoidFree_58
du_arr'45'a_194 v0
  = case coe v0 of
      C_vf'45'arr_92 v11 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.arr-b
d_arr'45'b_218 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'8849'π__6 ->
  T_VoidFree_58 -> T_VoidFree_58
d_arr'45'b_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_arr'45'b_218 v10
du_arr'45'b_218 :: T_VoidFree_58 -> T_VoidFree_58
du_arr'45'b_218 v0
  = case coe v0 of
      C_vf'45'arr_92 v11 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.prod-a
d_prod'45'a_234 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  T_VoidFree_58 -> T_VoidFree_58
d_prod'45'a_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_prod'45'a_234 v6
du_prod'45'a_234 :: T_VoidFree_58 -> T_VoidFree_58
du_prod'45'a_234 v0
  = case coe v0 of
      C_vf'45'prod_106 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.prod-b
d_prod'45'b_250 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  T_VoidFree_58 -> T_VoidFree_58
d_prod'45'b_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_prod'45'b_250 v6
du_prod'45'b_250 :: T_VoidFree_58 -> T_VoidFree_58
du_prod'45'b_250 v0
  = case coe v0 of
      C_vf'45'prod_106 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.sum-a
d_sum'45'a_266 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  T_VoidFree_58 -> T_VoidFree_58
d_sum'45'a_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sum'45'a_266 v6
du_sum'45'a_266 :: T_VoidFree_58 -> T_VoidFree_58
du_sum'45'a_266 v0
  = case coe v0 of
      C_vf'45'sum_120 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.sum-b
d_sum'45'b_282 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  T_VoidFree_58 -> T_VoidFree_58
d_sum'45'b_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sum'45'b_282 v6
du_sum'45'b_282 :: T_VoidFree_58 -> T_VoidFree_58
du_sum'45'b_282 v0
  = case coe v0 of
      C_vf'45'sum_120 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.voidFree?
d_voidFree'63'_292 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_voidFree'63'_292 v0 v1 v2
  = let v3
          = case coe v2 of
              MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'unit_62))
              MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'int_64))
              MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'float_66))
              MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'str_68))
              MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'buffer_70))
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C_Unit_118
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_Void_120
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'void_60))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C__'42'__122 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                         -> coe
                              du_two_142 (coe C_vf'45'prod_106)
                              (coe d_voidFree'63'_292 (coe v12) (coe v4) (coe v10))
                              (coe d_voidFree'63'_292 (coe v13) (coe v5) (coe v11))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C__'43'__124 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'sum_94 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                         -> coe
                              du_two_142 (coe C_vf'45'sum_120)
                              (coe d_voidFree'63'_292 (coe v12) (coe v4) (coe v10))
                              (coe d_voidFree'63'_292 (coe v13) (coe v5) (coe v11))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v14 v15 v16
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                         -> coe
                              du_two_142 (coe C_vf'45'arr_92)
                              (coe d_voidFree'63'_292 (coe v4) (coe v17) (coe v14))
                              (coe d_voidFree'63'_292 (coe v19) (coe v6) (coe v15))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'μ_98
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'μ_124))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_ν'45'type_130 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'ν_106 v9
                  -> case coe v0 of
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 v10 v11
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'ν_134))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_Int_132
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_Float_134
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_Str_136
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Type.C_Buffer_138
           -> case coe v2 of
                MAlonzo.Code.Once.Type.Sub.C_sub'45'void_48
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_50
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_62))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'int_52
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_64))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'float_54
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_66))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'str_56
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'str_68))
                MAlonzo.Code.Once.Type.Sub.C_sub'45'buffer_58
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'buffer_70))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.CoerceIR.erase-eq
d_erase'45'eq_314 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  T_VoidFree_58 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'45'eq_314 = erased
-- Once.Surface.CoerceIR.runCoe-dec
d_runCoe'45'dec_366 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_runCoe'45'dec_366 ~v0 v1 v2 v3 v4 v5
  = du_runCoe'45'dec_366 v1 v2 v3 v4 v5
du_runCoe'45'dec_366 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_runCoe'45'dec_366 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe seq (coe v6) (coe v4)
             else coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v0))
                       (d_coeIR_32 (coe v0) (coe v1) (coe v2)) v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.runCoe
d_runCoe_384 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_runCoe_384 ~v0 v1 v2 v3 v4 = du_runCoe_384 v1 v2 v3 v4
du_runCoe_384 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_runCoe_384 v0 v1 v2 v3
  = coe
      du_runCoe'45'dec_366 (coe v0) (coe v1) (coe v2)
      (coe d_voidFree'63'_292 (coe v0) (coe v1) (coe v2)) (coe v3)
