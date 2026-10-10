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

module MAlonzo.Code.Once.Adequacy.GradedRelation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.GradedDomain
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Denotation.ValueDomainLaws
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.GradedRelation._∼ᵖᵈ_
d__'8764''7510''7496'__14 a0 a1 a2 a3 = ()
data T__'8764''7510''7496'__14
  = C_constructor_26 MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
-- Once.Adequacy.GradedRelation._∼ᵖᵈ_.force-∼ᵖᵈ
d_force'45''8764''7510''7496'_24 ::
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_force'45''8764''7510''7496'_24 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGV
d_RelGV_30 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelGV_30 = erased
-- Once.Adequacy.GradedRelation.RelGT
d_RelGT_34 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGT_34 = erased
-- Once.Adequacy.GradedRelation.RelGM
d_RelGM_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGM_40 = erased
-- Once.Adequacy.GradedRelation.RelGT-return
d_RelGT'45'return_162 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelGT'45'return_162 ~v0 ~v1 ~v2 ~v3 v4
  = du_RelGT'45'return_162 v4
du_RelGT'45'return_162 ::
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelGT'45'return_162 v0
  = coe MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678 v0
-- Once.Adequacy.GradedRelation.RelGT-bind
d_RelGT'45'bind_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelGT'45'bind_182 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelGT'45'bind_182 v3 v4 v7 v8
du_RelGT'45'bind_182 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelGT'45'bind_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_422
      (coe v0) (coe v1) (coe v2) (coe (\ v4 v5 -> coe v3 v4 v5))
-- Once.Adequacy.GradedRelation.RelGᵖ-bind
d_RelG'7510''45'bind_222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelG'7510''45'bind_222 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelG'7510''45'bind_222 v3 v4 v7 v8
du_RelG'7510''45'bind_222 ::
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelG'7510''45'bind_222 v0 v1 v2 v3
  = coe
      du_RelGT'45'bind_182
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v0)
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.GradedRelation.RelGᵖᵉ-bind
d_RelG'7510''7497''45'bind_260 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelG'7510''7497''45'bind_260 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelG'7510''7497''45'bind_260 v3 v4 v7 v8
du_RelG'7510''7497''45'bind_260 ::
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelG'7510''7497''45'bind_260 v0 v1 v2 v3
  = coe
      du_RelGT'45'bind_182
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v0)
      (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.GradedRelation.RelGM-bind
d_RelGM'45'bind_298 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelGM'45'bind_298 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_RelGM'45'bind_298 v1 v4 v5
du_RelGM'45'bind_298 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelGM'45'bind_298 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe du_RelG'7510''45'bind_222 (coe v1) (coe v2)
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe du_RelGT'45'bind_182 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-return
d_RelGM'45'return_332 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelGM'45'return_332 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_RelGM'45'return_332 v1 v5
du_RelGM'45'return_332 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelGM'45'return_332 v0 v1
  = coe seq (coe v0) (coe du_RelGT'45'return_162 (coe v1))
-- Once.Adequacy.GradedRelation.prjB-rel
d_prjB'45'rel_350 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prjB'45'rel_350 = erased
-- Once.Adequacy.GradedRelation.injB-rel
d_injB'45'rel_390 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_injB'45'rel_390 ~v0 v1 v2 v3 = du_injB'45'rel_390 v1 v2 v3
du_injB'45'rel_390 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
du_injB'45'rel_390 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_injB'45'rel_390 (coe v7) (coe v5) (coe v9))
                           (coe du_injB'45'rel_390 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_injB'45'rel_390 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_injB'45'rel_390 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.injBᵍ-rel
d_injB'7501''45'rel_424 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_injB'7501''45'rel_424 ~v0 v1 v2 v3
  = du_injB'7501''45'rel_424 v1 v2 v3
du_injB'7501''45'rel_424 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
du_injB'7501''45'rel_424 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_injB'7501''45'rel_424 (coe v7) (coe v5) (coe v9))
                           (coe du_injB'7501''45'rel_424 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_injB'7501''45'rel_424 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_injB'7501''45'rel_424 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embν-∼
d_embν'45''8764'_458 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Denotation.GradedDomain.T_ν'7510'_74 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.ValueDomainLaws.T__'8764''7496'__12
d_embν'45''8764'_458 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomainLaws.C_constructor_24
      (coe
         d_embLayer_466 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Denotation.GradedDomain.d_force'7510'_80
            (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.d_force'7496'_14 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.embLayer
d_embLayer_466 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_embLayer_466 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
                    (d_mapEmbν'45''8764'_476
                       (coe v0) (coe v1) (coe v1) (coe v2) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbν-∼
d_mapEmbν'45''8764'_476 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'45''8764'_476 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe
             d_embν'45''8764'_458 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'45''8764'_476 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'45''8764'_476 (coe v0) (coe v1) (coe v7) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_mapEmbν'45''8764'_476 (coe v0) (coe v1) (coe v6) (coe v8)
                                     (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'45''8764'_476 (coe v0) (coe v1) (coe v7) (coe v9)
                                     (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-ret
d_RelGM'45'ret_542 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_RelGM'45'ret_542 ~v0 v1 ~v2 ~v3 ~v4 v5
  = du_RelGM'45'ret_542 v1 v5
du_RelGM'45'ret_542 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_RelGM'45'ret_542 v0 v1 = coe seq (coe v0) (coe v1)
