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

module MAlonzo.Code.Once.Adequacy.CataBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Adequacy.SeqRel
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CataBridge._.RelT
d_RelT_10 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_RelT_10 = erased
-- Once.Adequacy.CataBridge._.RelV
d_RelV_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelV_12 = erased
-- Once.Adequacy.CataBridge.base-refl
d_base'45'refl_24 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_base'45'refl_24 ~v0 v1 v2 v3 = du_base'45'refl_24 v1 v2 v3
du_base'45'refl_24 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
du_base'45'refl_24 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_base'45'refl_24 (coe v7) (coe v5) (coe v9))
                           (coe du_base'45'refl_24 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_base'45'refl_24 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_base'45'refl_24 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge.cata-bridge
d_cata'45'bridge_76 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'bridge_76 ~v0 v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 v10
  = du_cata'45'bridge_76 v1 v3 v4 v5 v6 v7 v10
du_cata'45'bridge_76 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'bridge_76 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v0))
      (\ v7 v8 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe
              MAlonzo.Code.Data.List.Base.du__'43''43'__32
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                       (coe v0) (coe v1) (coe v7))
                    v8))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    v2
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
                       (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                (coe v0) (coe v1) (coe v7))
                             v8)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v8
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                          (coe (0 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                                (coe
                                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                   (coe v0) (coe v1) (coe v7))
                                v8)))))))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe
                 v2
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
                    (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                             (coe v0) (coe v1) (coe v7))
                          v8)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v8
                    (coe
                       MAlonzo.Code.Data.List.Base.du_length_268
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                (coe v0) (coe v1) (coe v7))
                             v8)))))))
      (\ v7 v8 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe
              MAlonzo.Code.Data.List.Base.du__'43''43'__32
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                       (coe v0) (coe v1) (coe v7))
                    v8))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    v3
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
                       (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                (coe v0) (coe v1) (coe v7))
                             v8)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v8
                       (coe
                          MAlonzo.Code.Data.List.Base.du_foldr_216
                          (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                          (coe (0 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                                (coe
                                   MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                   (coe v0) (coe v1) (coe v7))
                                v8)))))))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe
                 v3
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
                    (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                             (coe v0) (coe v1) (coe v7))
                          v8)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v8
                    (coe
                       MAlonzo.Code.Data.List.Base.du_length_268
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 v0
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                                (coe v0) (coe v1) (coe v7))
                             v8)))))))
      (coe du_algR'45'full_216 (coe v0) (coe v1) (coe v4))
      (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_454
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v0)) (coe v5))
      v6
-- Once.Adequacy.CataBridge._.RelC
d_RelC_98 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_RelC_98 = erased
-- Once.Adequacy.CataBridge._.out-rel
d_out'45'rel_108 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_out'45'rel_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
                 v13
  = du_out'45'rel_108 v9 v10 v11 v12 v13
du_out'45'rel_108 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_out'45'rel_108 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v6 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__114 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_out'45'rel_108 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_out'45'rel_108 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__116 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_out'45'rel_108 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_out'45'rel_108 (coe v10) (coe v8) (coe v12) (coe v14)
                                            (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge._.z-rel
d_z'45'rel_164 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_z'45'rel_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
               v13
  = du_z'45'rel_164 v9 v10 v11 v12 v13
du_z'45'rel_164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_z'45'rel_164 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_110 v7
               -> coe
                    du_base'45'refl_24 (coe v7) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_458 (coe v7)
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__114 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_z'45'rel_164 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_z'45'rel_164 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__116 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_z'45'rel_164 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_z'45'rel_164 (coe v10) (coe v8) (coe v12) (coe v14)
                                            (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge._.algR-full
d_algR'45'full_216 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algR'45'full_216 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10 v11
  = du_algR'45'full_216 v1 v3 v6 v9 v10 v11
du_algR'45'full_216 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algR'45'full_216 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'bind_594
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 (coe v0)
         (coe
            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
            (coe v0) (coe v1) (coe v3)))
      (coe
         (\ v6 ->
            coe
              v2
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
                 (coe v0)
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                          (coe v0) (coe v1) (coe v3)))
                    (coe v6)))
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_714
                 (coe v0)
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                          (coe v0) (coe v1) (coe v4)))
                    (coe v6)))
              (coe
                 du_z'45'rel_164 (coe v0) (coe v1)
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                          (coe v0) (coe v1) (coe v3)))
                    (coe v6))
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_156 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
                          (coe v0) (coe v1) (coe v4)))
                    (coe v6))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe du_sq_228 v0 v1 v3 v4 v5 v6)))))
-- Once.Adequacy.CataBridge._._.sq
d_sq_228 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sq_228 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_sq_228 v1 v3 v9 v10 v11
du_sq_228 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sq_228 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.SeqRel.du_seqF'45'rel_128 (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_804
         (coe v0) (coe v1) (coe v3))
      (coe
         du_out'45'rel_108 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
