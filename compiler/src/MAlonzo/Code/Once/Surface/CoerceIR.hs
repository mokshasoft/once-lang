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
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Surface.CoerceIR.wrapArr
d_wrapArr_18 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_wrapArr_18 v0 ~v1 v2 v3 v4 ~v5 v6 v7
  = du_wrapArr_18 v0 v2 v3 v4 v6 v7
du_wrapArr_18 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_wrapArr_18 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28 v3 v5
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v1) (coe v0)
                  (coe v3))
               (coe v1))
            (coe MAlonzo.Code.Once.IR.C_apply_94)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4
                  (coe MAlonzo.Code.Once.IR.C_snd_48)))))
-- Once.Surface.CoerceIR.wrapArr₀
d_wrapArr'8320'_28 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_wrapArr'8320'_28 ~v0 ~v1 v2 ~v3 v4 = du_wrapArr'8320'_28 v2 v4
du_wrapArr'8320'_28 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_wrapArr'8320'_28 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1
         (coe MAlonzo.Code.Once.IR.C_apply_94))
-- Once.Surface.CoerceIR.coeIR
d_coeIR_38 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_coeIR_38 v0 v1 v2 v3
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
                                         du_wrapArr'8320'_28
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v16))
                                         (coe d_coeIR_38 (coe v0) (coe v16) (coe v21) (coe v12))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         du_wrapArr_18 (coe v18)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v14))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v19))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v16))
                                         (coe d_coeIR_38 (coe v0) (coe v19) (coe v14) (coe v11))
                                         (coe d_coeIR_38 (coe v0) (coe v16) (coe v21) (coe v12))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         du_wrapArr_18 (coe v18)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v14))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v19))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0)
                                            (coe v16))
                                         (coe d_coeIR_38 (coe v0) (coe v19) (coe v14) (coe v11))
                                         (coe d_coeIR_38 (coe v0) (coe v16) (coe v21) (coe v12))
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
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v10))
                              (d_coeIR_38 (coe v0) (coe v10) (coe v12) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v11))
                              (d_coeIR_38 (coe v0) (coe v11) (coe v13) (coe v9))
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
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v12))
                              (coe MAlonzo.Code.Once.IR.C_inl_54)
                              (d_coeIR_38 (coe v0) (coe v10) (coe v12) (coe v8)))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v13))
                              (coe MAlonzo.Code.Once.IR.C_inr_60)
                              (d_coeIR_38 (coe v0) (coe v11) (coe v13) (coe v9)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v7
        -> coe MAlonzo.Code.Once.IR.C_id_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.VoidFree
d_VoidFree_66 a0 a1 a2 a3 = ()
data T_VoidFree_66
  = C_vf'45'void_70 | C_vf'45'unit_72 | C_vf'45'int_74 |
    C_vf'45'float_76 | C_vf'45'var_80 |
    C_vf'45'arr_100 T_VoidFree_66 T_VoidFree_66 |
    C_vf'45'prod_114 T_VoidFree_66 T_VoidFree_66 |
    C_vf'45'sum_128 T_VoidFree_66 T_VoidFree_66 | C_vf'45'μ_132 |
    C_vf'45'ν_142
-- Once.Surface.CoerceIR.two
d_two_150 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_two_150 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 = du_two_150 v3 v6 v7
du_two_150 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_two_150 v0 v1 v2
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
d_arr'45'a_204 ::
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
  T_VoidFree_66 -> T_VoidFree_66
d_arr'45'a_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_arr'45'a_204 v11
du_arr'45'a_204 :: T_VoidFree_66 -> T_VoidFree_66
du_arr'45'a_204 v0
  = case coe v0 of
      C_vf'45'arr_100 v10 v11 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.arr-b
d_arr'45'b_230 ::
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
  T_VoidFree_66 -> T_VoidFree_66
d_arr'45'b_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_arr'45'b_230 v11
du_arr'45'b_230 :: T_VoidFree_66 -> T_VoidFree_66
du_arr'45'b_230 v0
  = case coe v0 of
      C_vf'45'arr_100 v10 v11 -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.prod-a
d_prod'45'a_248 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_66 -> T_VoidFree_66
d_prod'45'a_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_prod'45'a_248 v7
du_prod'45'a_248 :: T_VoidFree_66 -> T_VoidFree_66
du_prod'45'a_248 v0
  = case coe v0 of
      C_vf'45'prod_114 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.prod-b
d_prod'45'b_266 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_66 -> T_VoidFree_66
d_prod'45'b_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_prod'45'b_266 v7
du_prod'45'b_266 :: T_VoidFree_66 -> T_VoidFree_66
du_prod'45'b_266 v0
  = case coe v0 of
      C_vf'45'prod_114 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.sum-a
d_sum'45'a_284 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_66 -> T_VoidFree_66
d_sum'45'a_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sum'45'a_284 v7
du_sum'45'a_284 :: T_VoidFree_66 -> T_VoidFree_66
du_sum'45'a_284 v0
  = case coe v0 of
      C_vf'45'sum_128 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.sum-b
d_sum'45'b_302 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_66 -> T_VoidFree_66
d_sum'45'b_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sum'45'b_302 v7
du_sum'45'b_302 :: T_VoidFree_66 -> T_VoidFree_66
du_sum'45'b_302 v0
  = case coe v0 of
      C_vf'45'sum_128 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.voidFree?
d_voidFree'63'_314 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_voidFree'63'_314 ~v0 v1 v2 v3 = du_voidFree'63'_314 v1 v2 v3
du_voidFree'63'_314 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_voidFree'63'_314 v0 v1 v2
  = let v3
          = case coe v2 of
              MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'unit_72))
              MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'int_74))
              MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                -> coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                        (coe C_vf'45'float_76))
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
                                 (coe C_vf'45'var_80))
                       _ -> coe v3
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Spec.Type.C_Void_20
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'void_70))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C__'42'__22 v12 v13
                         -> coe
                              du_two_150 (coe C_vf'45'prod_114)
                              (coe du_voidFree'63'_314 (coe v12) (coe v4) (coe v10))
                              (coe du_voidFree'63'_314 (coe v13) (coe v5) (coe v11))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v10 v11
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
                         -> coe
                              du_two_150 (coe C_vf'45'sum_128)
                              (coe du_voidFree'63'_314 (coe v12) (coe v4) (coe v10))
                              (coe du_voidFree'63'_314 (coe v13) (coe v5) (coe v11))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v14 v15 v16
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
                         -> case coe v18 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                                -> case coe v5 of
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                                       -> let v24
                                                = MAlonzo.Code.Once.Type.DecEq.d__'8799'p__10
                                                    (coe v21) (coe v23) in
                                          coe
                                            (case coe v24 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                 -> if coe v25
                                                      then coe
                                                             seq (coe v26)
                                                             (coe
                                                                du_two_150 (coe C_vf'45'arr_100)
                                                                (coe
                                                                   du_voidFree'63'_314 (coe v4)
                                                                   (coe v17) (coe v14))
                                                                (coe
                                                                   du_voidFree'63'_314 (coe v19)
                                                                   (coe v6) (coe v15)))
                                                      else coe
                                                             seq (coe v26)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                (coe v25)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'μ_132))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v9
                  -> case coe v0 of
                       MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
                         -> coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                              (coe
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                 (coe C_vf'45'ν_142))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
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
                          (coe C_vf'45'unit_72))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'int_74))
                MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                          (coe C_vf'45'float_76))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Surface.CoerceIR.erase-eq
d_erase'45'eq_370 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  T_VoidFree_66 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'45'eq_370 = erased
-- Once.Surface.CoerceIR.runCoe-dec
d_runCoe'45'dec_432 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_runCoe'45'dec_432 v0 v1 v2 ~v3 v4 v5 v6
  = du_runCoe'45'dec_432 v0 v1 v2 v4 v5 v6
du_runCoe'45'dec_432 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_runCoe'45'dec_432 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe seq (coe v7) (coe v5)
             else coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v0) (coe v1))
                       (d_coeIR_38 (coe v0) (coe v1) (coe v2) (coe v3)) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.CoerceIR.runCoe
d_runCoe_452 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_runCoe_452 v0 v1 v2 ~v3 v4 v5 = du_runCoe_452 v0 v1 v2 v4 v5
du_runCoe_452 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_runCoe_452 v0 v1 v2 v3 v4
  = coe
      du_runCoe'45'dec_432 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_voidFree'63'_314 (coe v1) (coe v2) (coe v3)) (coe v4)
