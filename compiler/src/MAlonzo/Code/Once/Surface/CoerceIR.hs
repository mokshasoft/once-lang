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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
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
d_coeIR_34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_coeIR_34 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe MAlonzo.Code.Once.IR.C_initial_76
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v19 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         du_wrapArr'8320'_24
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v16))
                                         (coe d_coeIR_34 (coe v0) (coe v16) (coe v21) (coe v12))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         du_wrapArr_14
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v14))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v19))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v16))
                                         (coe d_coeIR_34 (coe v0) (coe v19) (coe v14) (coe v11))
                                         (coe d_coeIR_34 (coe v0) (coe v16) (coe v21) (coe v12))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         du_wrapArr_14
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v14))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v19))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v16))
                                         (coe d_coeIR_34 (coe v0) (coe v19) (coe v14) (coe v11))
                                         (coe d_coeIR_34 (coe v0) (coe v16) (coe v21) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v10))
                              (d_coeIR_34 (coe v0) (coe v10) (coe v12) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v11))
                              (d_coeIR_34 (coe v0) (coe v11) (coe v13) (coe v9))
                              (coe MAlonzo.Code.Once.IR.C_snd_48))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
                      -> coe
                           MAlonzo.Code.Once.IR.C_case_68
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v12))
                              (coe MAlonzo.Code.Once.IR.C_inl_54)
                              (d_coeIR_34 (coe v0) (coe v10) (coe v12) (coe v8)))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v13))
                              (coe MAlonzo.Code.Once.IR.C_inr_60)
                              (d_coeIR_34 (coe v0) (coe v11) (coe v13) (coe v9)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v7
        -> coe MAlonzo.Code.Once.IR.C_id_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.VoidFree
d_VoidFree_62 a0 a1 a2 a3 = ()
data T_VoidFree_62
  = C_vf'45'void_66 | C_vf'45'unit_68 | C_vf'45'int_70 |
    C_vf'45'float_72 | C_vf'45'var_76 |
    C_vf'45'arr_98 T_VoidFree_62 T_VoidFree_62 |
    C_vf'45'prod_112 T_VoidFree_62 T_VoidFree_62 |
    C_vf'45'sum_126 T_VoidFree_62 T_VoidFree_62 | C_vf'45'μ_130 |
    C_vf'45'ν_140
-- Once.Surface.CoerceIR.two
d_two_148 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_two_148 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 = du_two_148 v3 v6 v7
du_two_148 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_two_148 v0 v1 v2
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
d_arr'45'a_202 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  T_VoidFree_62 -> T_VoidFree_62
d_arr'45'a_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_arr'45'a_202 v11
du_arr'45'a_202 :: T_VoidFree_62 -> T_VoidFree_62
du_arr'45'a_202 v0
  = case coe v0 of
      C_vf'45'arr_98 v11 v12 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.arr-b
d_arr'45'b_228 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  T_VoidFree_62 -> T_VoidFree_62
d_arr'45'b_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_arr'45'b_228 v11
du_arr'45'b_228 :: T_VoidFree_62 -> T_VoidFree_62
du_arr'45'b_228 v0
  = case coe v0 of
      C_vf'45'arr_98 v11 v12 -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.prod-a
d_prod'45'a_246 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_62 -> T_VoidFree_62
d_prod'45'a_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_prod'45'a_246 v7
du_prod'45'a_246 :: T_VoidFree_62 -> T_VoidFree_62
du_prod'45'a_246 v0
  = case coe v0 of
      C_vf'45'prod_112 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.prod-b
d_prod'45'b_264 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_62 -> T_VoidFree_62
d_prod'45'b_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_prod'45'b_264 v7
du_prod'45'b_264 :: T_VoidFree_62 -> T_VoidFree_62
du_prod'45'b_264 v0
  = case coe v0 of
      C_vf'45'prod_112 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.sum-a
d_sum'45'a_282 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_62 -> T_VoidFree_62
d_sum'45'a_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sum'45'a_282 v7
du_sum'45'a_282 :: T_VoidFree_62 -> T_VoidFree_62
du_sum'45'a_282 v0
  = case coe v0 of
      C_vf'45'sum_126 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.sum-b
d_sum'45'b_300 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_62 -> T_VoidFree_62
d_sum'45'b_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sum'45'b_300 v7
du_sum'45'b_300 :: T_VoidFree_62 -> T_VoidFree_62
du_sum'45'b_300 v0
  = case coe v0 of
      C_vf'45'sum_126 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.voidFree?
d_voidFree'63'_312 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_voidFree'63'_312 ~v0 v1 v2 v3 = du_voidFree'63'_312 v1 v2 v3
du_voidFree'63'_312 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_voidFree'63'_312 v0 v1 v2
  = let v3
          = case coe v2 of
              MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'unit_68))
              MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'int_70))
              MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'float_72))
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C_var_16 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C_var_16 v6
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'var_76))
                       _ -> coe v3
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_Unit_18
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_Void_20
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'void_66))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C__'42'__22 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
                         -> coe
                              du_two_148 (coe C_vf'45'prod_112)
                              (coe du_voidFree'63'_312 (coe v12) (coe v4) (coe v10))
                              (coe du_voidFree'63'_312 (coe v13) (coe v5) (coe v11))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C__'43'__24 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
                         -> coe
                              du_two_148 (coe C_vf'45'sum_126)
                              (coe du_voidFree'63'_312 (coe v12) (coe v4) (coe v10))
                              (coe du_voidFree'63'_312 (coe v13) (coe v5) (coe v11))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v14 v15 v16
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
                         -> coe
                              du_two_148 (coe C_vf'45'arr_98)
                              (coe du_voidFree'63'_312 (coe v4) (coe v17) (coe v14))
                              (coe du_voidFree'63'_312 (coe v19) (coe v6) (coe v15))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_μ_28 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'μ_130))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_ν_30 v4 v5
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v9
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'ν_140))
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_Int_32
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_Float_34
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_68))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_72))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.CoerceIR.erase-eq
d_erase'45'eq_336 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_62 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'45'eq_336 = erased
-- Once.Surface.CoerceIR.runCoe-dec
d_runCoe'45'dec_390 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_runCoe'45'dec_390 v0 v1 v2 ~v3 v4 v5 v6
  = du_runCoe'45'dec_390 v0 v1 v2 v4 v5 v6
du_runCoe'45'dec_390 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_runCoe'45'dec_390 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe seq (coe v7) (coe v5)
             else coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v1))
                       (d_coeIR_34 (coe v0) (coe v1) (coe v2) (coe v3)) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.runCoe
d_runCoe_410 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_runCoe_410 v0 v1 v2 ~v3 v4 v5 = du_runCoe_410 v0 v1 v2 v4 v5
du_runCoe_410 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_runCoe_410 v0 v1 v2 v3 v4
  = coe
      du_runCoe'45'dec_390 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_voidFree'63'_312 (coe v1) (coe v2) (coe v3)) (coe v4)
