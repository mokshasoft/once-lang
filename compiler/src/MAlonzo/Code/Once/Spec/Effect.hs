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

module MAlonzo.Code.Once.Spec.Effect where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Signature

-- Once.Spec.Effect.Step
d_Step_12 a0 a1 a2 = ()
data T_Step_12
  = C_done_18 AgdaAny |
    C_node_20 MAlonzo.Code.Once.Spec.Signature.T_Layer_236
-- Once.Spec.Effect.T
d_T_24 a0 a1 = ()
newtype T_T_24 = C_roll_28 T_Step_12
-- Once.Spec.Effect.returnT
d_returnT_32 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> AgdaAny -> T_T_24
d_returnT_32 ~v0 ~v1 v2 = du_returnT_32 v2
du_returnT_32 :: AgdaAny -> T_T_24
du_returnT_32 v0 = coe C_roll_28 (coe C_done_18 (coe v0))
-- Once.Spec.Effect._>>=T_
d__'62''62''61'T__40 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> () -> T_T_24 -> (AgdaAny -> T_T_24) -> T_T_24
d__'62''62''61'T__40 ~v0 ~v1 ~v2 v3 v4
  = du__'62''62''61'T__40 v3 v4
du__'62''62''61'T__40 :: T_T_24 -> (AgdaAny -> T_T_24) -> T_T_24
du__'62''62''61'T__40 v0 v1
  = case coe v0 of
      C_roll_28 v2
        -> case coe v2 of
             C_done_18 v3 -> coe v1 v3
             C_node_20 v3
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Signature.C_call_244 v4 v5 v6
                      -> coe
                           C_roll_28
                           (coe
                              C_node_20
                              (coe
                                 MAlonzo.Code.Once.Spec.Signature.C_call_244 (coe v4) (coe v5)
                                 (coe (\ v7 -> coe du__'62''62''61'T__40 (coe v6 v7) (coe v1)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.mapT
d_mapT_60 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> () -> (AgdaAny -> AgdaAny) -> T_T_24 -> T_T_24
d_mapT_60 ~v0 ~v1 ~v2 v3 v4 = du_mapT_60 v3 v4
du_mapT_60 :: (AgdaAny -> AgdaAny) -> T_T_24 -> T_T_24
du_mapT_60 v0 v1
  = coe
      du__'62''62''61'T__40 (coe v1)
      (coe (\ v2 -> coe du_returnT_32 (coe v0 v2)))
-- Once.Spec.Effect.Mᶠ
d_M'7584'_68 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 -> () -> ()
d_M'7584'_68 = erased
-- Once.Spec.Effect.νM
d_νM_78 a0 a1 a2 = ()
data T_νM_78 = C_constructor_88 AgdaAny
-- Once.Spec.Effect.νM.outν
d_outν_86 :: T_νM_78 -> AgdaAny
d_outν_86 v0
  = case coe v0 of
      C_constructor_88 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.ana
d_ana_96 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_νM_78
d_ana_96 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
        -> coe (\ v2 v3 v4 v5 -> coe du_anaP_102 (coe v0) v2 v4 v5)
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
        -> coe (\ v2 v3 v4 v5 -> coe du_anaA_168 (coe v0) v2 v4 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.anaP
d_anaP_102 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_νM_78
d_anaP_102 v0 v1 ~v2 v3 v4 = du_anaP_102 v0 v1 v3 v4
du_anaP_102 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_νM_78
du_anaP_102 v0 v1 v2 v3
  = coe
      C_constructor_88
      (coe du_mapP_110 (coe v0) (coe v1) (coe v1) (coe v2) (coe v2 v3))
-- Once.Spec.Effect.mapP
d_mapP_110 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_mapP_110 v0 v1 v2 ~v3 v4 v5 = du_mapP_110 v0 v1 v2 v4 v5
du_mapP_110 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_mapP_110 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v4
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_anaP_102 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapP_110 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapP_110 (coe v0) (coe v1) (coe v6) (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapP_110 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
                    (coe du_mapP_110 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.anaA
d_anaA_168 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T_24) -> AgdaAny -> T_νM_78
d_anaA_168 v0 v1 ~v2 v3 v4 = du_anaA_168 v0 v1 v3 v4
du_anaA_168 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T_24) -> AgdaAny -> T_νM_78
du_anaA_168 v0 v1 v2 v3
  = coe
      C_constructor_88
      (coe du_treeA_174 (coe v0) (coe v1) (coe v2) (coe v2 v3))
-- Once.Spec.Effect.treeA
d_treeA_174 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T_24) -> T_T_24 -> T_T_24
d_treeA_174 v0 v1 ~v2 v3 v4 = du_treeA_174 v0 v1 v3 v4
du_treeA_174 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T_24) -> T_T_24 -> T_T_24
du_treeA_174 v0 v1 v2 v3
  = case coe v3 of
      C_roll_28 v4
        -> case coe v4 of
             C_done_18 v5
               -> coe
                    C_roll_28
                    (coe
                       C_done_18
                       (coe du_mapA_182 (coe v0) (coe v1) (coe v1) (coe v2) (coe v5)))
             C_node_20 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Signature.C_call_244 v6 v7 v8
                      -> coe
                           C_roll_28
                           (coe
                              C_node_20
                              (coe
                                 MAlonzo.Code.Once.Spec.Signature.C_call_244 (coe v6) (coe v7)
                                 (coe
                                    (\ v9 ->
                                       coe du_treeA_174 (coe v0) (coe v1) (coe v2) (coe v8 v9)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.mapA
d_mapA_182 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T_24) -> AgdaAny -> AgdaAny
d_mapA_182 v0 v1 v2 ~v3 v4 v5 = du_mapA_182 v0 v1 v2 v4 v5
du_mapA_182 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T_24) -> AgdaAny -> AgdaAny
du_mapA_182 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v4
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_anaA_168 (coe v0) (coe v1) (coe v3) (coe v4)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapA_182 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapA_182 (coe v0) (coe v1) (coe v6) (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapA_182 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
                    (coe du_mapA_182 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.LayerEq
d_LayerEq_258 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_LayerEq_258 = erased
-- Once.Spec.Effect.BlockEq
d_BlockEq_324 a0 a1 a2 a3 a4 = ()
data T_BlockEq_324
  = C_done'8776'_334 AgdaAny |
    C_node'8776'_346 (AgdaAny -> T_BlockEq_324)
-- Once.Spec.Effect.EqLayer
d_EqLayer_352 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_EqLayer_352 = erased
-- Once.Spec.Effect._≈ν_
d__'8776'ν__366 a0 a1 a2 a3 a4 = ()
data T__'8776'ν__366 = C_constructor_380 AgdaAny
-- Once.Spec.Effect._≈ν_.force≈
d_force'8776'_378 :: T__'8776'ν__366 -> AgdaAny
d_force'8776'_378 v0
  = case coe v0 of
      C_constructor_380 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.T∞
d_T'8734'_382 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] -> () -> ()
d_T'8734'_382 = erased
-- Once.Spec.Effect.force
d_force_388 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> T_νM_78 -> T_T_24
d_force_388 ~v0 ~v1 v2 = du_force_388 v2
du_force_388 :: T_νM_78 -> T_T_24
du_force_388 v0 = coe d_outν_86 (coe v0)
-- Once.Spec.Effect._≈_
d__'8776'__392 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> T_νM_78 -> T_νM_78 -> ()
d__'8776'__392 = erased
-- Once.Spec.Effect.return∞
d_return'8734'_396 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> AgdaAny -> T_νM_78
d_return'8734'_396 ~v0 ~v1 v2 = du_return'8734'_396 v2
du_return'8734'_396 :: AgdaAny -> T_νM_78
du_return'8734'_396 v0
  = coe
      C_constructor_88
      (coe
         du_returnT_32
         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0)))
-- Once.Spec.Effect._>>=∞_
d__'62''62''61''8734'__404 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> () -> T_νM_78 -> (AgdaAny -> T_νM_78) -> T_νM_78
d__'62''62''61''8734'__404 v0 ~v1 ~v2 v3 v4
  = du__'62''62''61''8734'__404 v0 v3 v4
du__'62''62''61''8734'__404 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_νM_78 -> (AgdaAny -> T_νM_78) -> T_νM_78
du__'62''62''61''8734'__404 v0 v1 v2
  = coe
      C_constructor_88
      (coe du_bindBlock_410 (coe v0) (coe d_outν_86 (coe v1)) (coe v2))
-- Once.Spec.Effect.bindBlock
d_bindBlock_410 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> () -> T_T_24 -> (AgdaAny -> T_νM_78) -> T_T_24
d_bindBlock_410 v0 ~v1 ~v2 v3 v4 = du_bindBlock_410 v0 v3 v4
du_bindBlock_410 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  T_T_24 -> (AgdaAny -> T_νM_78) -> T_T_24
du_bindBlock_410 v0 v1 v2
  = case coe v1 of
      C_roll_28 v3
        -> case coe v3 of
             C_done_18 v4
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                      -> coe d_outν_86 (coe v2 v5)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                      -> coe
                           C_roll_28
                           (coe
                              C_done_18
                              (coe
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                 (coe du__'62''62''61''8734'__404 (coe v0) (coe v5) (coe v2))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_node_20 v4
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Signature.C_call_244 v5 v6 v7
                      -> coe
                           C_roll_28
                           (coe
                              C_node_20
                              (coe
                                 MAlonzo.Code.Once.Spec.Signature.C_call_244 (coe v5) (coe v6)
                                 (coe
                                    (\ v8 -> coe du_bindBlock_410 (coe v0) (coe v7 v8) (coe v2)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.embed
d_embed_436 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> T_T_24 -> T_νM_78
d_embed_436 ~v0 ~v1 v2 = du_embed_436 v2
du_embed_436 :: T_T_24 -> T_νM_78
du_embed_436 v0
  = coe
      C_constructor_88
      (coe
         du_mapT_60 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
         (coe v0))
-- Once.Spec.Effect.loop
d_loop_444 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> () -> (AgdaAny -> T_T_24) -> AgdaAny -> T_νM_78
d_loop_444 v0 ~v1 ~v2 v3 = du_loop_444 v0 v3
du_loop_444 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  (AgdaAny -> T_T_24) -> AgdaAny -> T_νM_78
du_loop_444 v0 v1
  = coe
      d_ana_96 v0 (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)
      (coe
         MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12
         (coe MAlonzo.Code.Once.Spec.Polynomial.C_SK_8)
         (coe MAlonzo.Code.Once.Spec.Polynomial.C_SId_10))
      erased v1
-- Once.Spec.Effect.M
d_M_450 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> () -> ()
d_M_450 = erased
-- Once.Spec.Effect.bind
d_bind_464 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bind_464 v0 v1 ~v2 ~v3 v4 v5 = du_bind_464 v0 v1 v4 v5
du_bind_464 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_bind_464 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v4
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v3 v2
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe du__'62''62''61'T__40 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe du__'62''62''61''8734'__404 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.sub
d_sub_484 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  () -> AgdaAny -> AgdaAny
d_sub_484 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_sub_484 v3 v5
du_sub_484 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny -> AgdaAny
du_sub_484 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe du_returnT_32 (coe v1)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> coe du_return'8734'_396 (coe v1)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
        -> coe du_embed_436 (coe v1)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.return
d_return_502 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () -> AgdaAny -> AgdaAny
d_return_502 ~v0 v1 ~v2 v3 = du_return_502 v1 v3
du_return_502 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> AgdaAny -> AgdaAny
du_return_502 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v1
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe du_returnT_32 (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe du_return'8734'_396 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.fmap
d_fmap_516 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_516 v0 v1 ~v2 ~v3 v4 v5 = du_fmap_516 v0 v1 v4 v5
du_fmap_516 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_516 v0 v1 v2 v3
  = coe
      du_bind_464 (coe v0) (coe v1) (coe v3)
      (coe (\ v4 -> coe du_return_502 (coe v1) (coe v2 v4)))
-- Once.Spec.Effect.toT∞
d_toT'8734'_530 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () -> AgdaAny -> T_νM_78
d_toT'8734'_530 ~v0 v1 ~v2 v3 = du_toT'8734'_530 v1 v3
du_toT'8734'_530 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 -> AgdaAny -> T_νM_78
du_toT'8734'_530 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe du_return'8734'_396 (coe v1)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe du_embed_436 (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.bindᵍ
d_bind'7501'_546 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_bind'7501'_546 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_bind'7501'_546 v0 v1 v2 v5 v6
du_bind'7501'_546 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_bind'7501'_546 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v5
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36 -> coe v4 v3
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Grade.C_fin_42 v6
                      -> case coe v6 of
                           MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                             -> coe
                                  du__'62''62''61'T__40 (coe v3)
                                  (coe (\ v7 -> coe du_returnT_32 (coe v4 v7)))
                           MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                             -> coe du__'62''62''61'T__40 (coe v3) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Spec.Grade.C_eff_44
                      -> coe
                           du__'62''62''61''8734'__404 (coe v0) (coe du_embed_436 (coe v3))
                           (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_fin_42 v5
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                      -> coe
                           du__'62''62''61''8734'__404 (coe v0) (coe v3)
                           (coe (\ v6 -> coe du_return'8734'_396 (coe v4 v6)))
                    MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                      -> coe
                           du__'62''62''61''8734'__404 (coe v0) (coe v3)
                           (coe (\ v6 -> coe du_embed_436 (coe v4 v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Grade.C_eff_44
               -> coe du__'62''62''61''8734'__404 (coe v0) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Effect.EqM
d_EqM_588 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () -> AgdaAny -> AgdaAny -> ()
d_EqM_588 = erased
-- Once.Spec.Effect.performT
d_performT_598 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  () -> MAlonzo.Code.Once.Spec.Signature.T_Layer_236 -> T_T_24
d_performT_598 ~v0 ~v1 v2 = du_performT_598 v2
du_performT_598 ::
  MAlonzo.Code.Once.Spec.Signature.T_Layer_236 -> T_T_24
du_performT_598 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Signature.C_call_244 v1 v2 v3
        -> coe
             C_roll_28
             (coe
                C_node_20
                (coe
                   MAlonzo.Code.Once.Spec.Signature.C_call_244 (coe v1) (coe v2)
                   (coe (\ v4 -> coe du_returnT_32 (coe v3 v4)))))
      _ -> MAlonzo.RTE.mazUnreachableError
