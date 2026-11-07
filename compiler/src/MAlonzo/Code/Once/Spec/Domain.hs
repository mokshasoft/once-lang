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

module MAlonzo.Code.Once.Spec.Domain where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Effect
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Domain._.M
d_M_10 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> () -> ()
d_M_10 = erased
-- Once.Spec.Domain._.νM
d_νM_30 a0 a1 a2 = ()
-- Once.Spec.Domain._.νM.outν
d_outν_40 :: MAlonzo.Code.Once.Spec.Effect.T_νM_78 -> AgdaAny
d_outν_40 v0 = coe MAlonzo.Code.Once.Spec.Effect.d_outν_86 (coe v0)
-- Once.Spec.Domain.⟦_⟧ᵛ
d_'10214'_'10215''7515'_42 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7515'_42 = erased
-- Once.Spec.Domain.code
d_code_44 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6
d_code_44 ~v0 v1 = du_code_44 v1
du_code_44 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6
du_code_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1
        -> coe MAlonzo.Code.Once.Spec.Polynomial.C_SK_8
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12
             (coe du_code_44 (coe v1)) (coe du_code_44 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14
             (coe du_code_44 (coe v1)) (coe du_code_44 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain._.toB
d_toB_98 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 -> AgdaAny -> AgdaAny
d_toB_98 ~v0 ~v1 ~v2 v3 v4 = du_toB_98 v3 v4
du_toB_98 ::
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 -> AgdaAny -> AgdaAny
du_toB_98 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Signature.C_unit_8 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C_void_10 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C_int_12 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C_float_14 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C__'42'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_toB_98 (coe v2) (coe v4)) (coe du_toB_98 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Signature.C__'43'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_toB_98 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_toB_98 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain._.fromB
d_fromB_102 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 -> AgdaAny -> AgdaAny
d_fromB_102 ~v0 ~v1 ~v2 v3 v4 = du_fromB_102 v3 v4
du_fromB_102 ::
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6 -> AgdaAny -> AgdaAny
du_fromB_102 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Signature.C_unit_8 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C_void_10 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C_int_12 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C_float_14 -> coe v1
      MAlonzo.Code.Once.Spec.Signature.C__'42'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_fromB_102 (coe v2) (coe v4))
                    (coe du_fromB_102 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Signature.C__'43'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_fromB_102 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_fromB_102 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain._.toL
d_toL_164 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_toL_164 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_toL_164 v3 v5
du_toL_164 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> AgdaAny
du_toL_164 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_toL_164 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_toL_164 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_toL_164 (coe v2) (coe v4))
                    (coe du_toL_164 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain._.fromL
d_fromL_170 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_fromL_170 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_fromL_170 v3 v5
du_fromL_170 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> AgdaAny
du_fromL_170 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_fromL_170 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_fromL_170 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_fromL_170 (coe v2) (coe v4))
                    (coe du_fromL_170 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain.foldM
d_foldM_250 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_foldM_250 v0 v1 v2 ~v3 v4 v5 = du_foldM_250 v0 v1 v2 v4 v5
du_foldM_250 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
du_foldM_250 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Polynomial.C_inS_86 v5
        -> coe
             MAlonzo.Code.Once.Spec.Effect.du_bind_520 (coe v0) (coe v1)
             (coe
                du_layerM_260 (coe v0) (coe v1) (coe v2) (coe v2) (coe v3)
                (coe v5))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain.layerM
d_layerM_260 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_layerM_260 v0 v1 v2 v3 ~v4 v5 v6
  = du_layerM_260 v0 v1 v2 v3 v5 v6
du_layerM_260 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_layerM_260 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8
        -> coe
             MAlonzo.Code.Once.Spec.Effect.du_return_558 (coe v1) (coe v5)
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_foldM_250 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe
                       du_layerM_260 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4)
                       (coe v8))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe
                       du_layerM_260 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Once.Spec.Effect.du_bind_520 (coe v0) (coe v1)
                    (coe
                       du_layerM_260 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4)
                       (coe v8))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Spec.Effect.du_bind_520 (coe v0) (coe v1)
                            (coe
                               du_layerM_260 (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
                               (coe v9))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Once.Spec.Effect.du_return_558 (coe v1)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                       (coe v11))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain.subν
d_subν_336 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Effect.T_νM_78 ->
  MAlonzo.Code.Once.Spec.Effect.T_νM_78
d_subν_336 v0 ~v1 ~v2 v3 v4 v5 = du_subν_336 v0 v3 v4 v5
du_subν_336 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Effect.T_νM_78 ->
  MAlonzo.Code.Once.Spec.Effect.T_νM_78
du_subν_336 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v3
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe
             MAlonzo.Code.Once.Spec.Effect.d_ana_96 v0
             (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38) v2 erased
             (\ v4 ->
                coe
                  MAlonzo.Code.Once.Spec.Effect.du_returnT_32
                  (coe MAlonzo.Code.Once.Spec.Effect.d_outν_86 (coe v4)))
             v3
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain.conv
d_conv_360 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> AgdaAny -> AgdaAny
d_conv_360 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'var_18 -> coe v6
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20 -> coe v6
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22 -> coe v6
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24 -> coe v6
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v14 v15 v16
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v4 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v22 v23 v24
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Spec.Effect.du_sub_540 (coe v16)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0)
                                                 (coe v21)
                                                 (coe
                                                    d_conv_360 (coe v0) (coe v1) (coe v2) (coe v19)
                                                    (coe v24) (coe v15))
                                                 (coe v6 v25)))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Spec.Effect.du_sub_540 (coe v16)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0)
                                                 (coe v21)
                                                 (coe
                                                    d_conv_360 (coe v0) (coe v1) (coe v2) (coe v19)
                                                    (coe v24) (coe v15))
                                                 (coe
                                                    v6
                                                    (d_conv_360
                                                       (coe v0) (coe v1) (coe v2) (coe v22)
                                                       (coe v17) (coe v14) (coe v25)))))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Spec.Effect.du_sub_540 (coe v16)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0)
                                                 (coe v21)
                                                 (coe
                                                    d_conv_360 (coe v0) (coe v1) (coe v2) (coe v19)
                                                    (coe v24) (coe v15))
                                                 (coe
                                                    v6
                                                    (d_conv_360
                                                       (coe v0) (coe v1) (coe v2) (coe v22)
                                                       (coe v17) (coe v14) (coe v25)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''42'_50 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_conv_360 (coe v0) (coe v1) (coe v2) (coe v13) (coe v15)
                                     (coe v11) (coe v17))
                                  (coe
                                     d_conv_360 (coe v0) (coe v1) (coe v2) (coe v14) (coe v16)
                                     (coe v12) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45''43'_60 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v15 v16
                      -> case coe v6 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe
                                     d_conv_360 (coe v0) (coe v1) (coe v2) (coe v13) (coe v15)
                                     (coe v11) (coe v17))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe
                                     d_conv_360 (coe v0) (coe v1) (coe v2) (coe v14) (coe v16)
                                     (coe v12) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'μ_64 -> coe v6
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'ν_72 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v11 v12
               -> coe
                    du_subν_336 (coe v0) (coe v10)
                    (coe
                       du_code_44
                       (coe
                          MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'F_160 (coe v1)
                          (coe (0 :: Integer)) (coe v11) (coe v2)))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Domain.traverseM
d_traverseM_470 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_traverseM_470 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_traverseM_470 v0 v1 v2 v5 v6
du_traverseM_470 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_traverseM_470 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8
        -> coe
             MAlonzo.Code.Once.Spec.Effect.du_return_558 (coe v1) (coe v4)
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10 -> coe v3 v4
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_traverseM_470 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Effect.du_fmap_572 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_traverseM_470 (coe v0) (coe v1) (coe v6) (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Effect.du_bind_520 (coe v0) (coe v1)
                    (coe du_traverseM_470 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
                    (coe
                       (\ v9 ->
                          coe
                            MAlonzo.Code.Once.Spec.Effect.du_bind_520 (coe v0) (coe v1)
                            (coe du_traverseM_470 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
                            (coe
                               (\ v10 ->
                                  coe
                                    MAlonzo.Code.Once.Spec.Effect.du_return_558 (coe v1)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                       (coe v10))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
