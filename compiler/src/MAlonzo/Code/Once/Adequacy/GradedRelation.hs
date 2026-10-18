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
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomainLaws
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.GradedRelation._∼ᵖᵈ_
d__'8764''7510''7496'__14 a0 a1 a2 a3 = ()
data T__'8764''7510''7496'__14
  = C_constructor_26 MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
-- Once.Adequacy.GradedRelation._∼ᵖᵈ_.force-∼ᵖᵈ
d_force'45''8764''7510''7496'_24 ::
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_force'45''8764''7510''7496'_24 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGV
d_RelGV_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_30 = erased
-- Once.Adequacy.GradedRelation.RelGT
d_RelGT_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGT_34 = erased
-- Once.Adequacy.GradedRelation.RelGM
d_RelGM_40 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGM_40 = erased
-- Once.Adequacy.GradedRelation.RelGT-return
d_RelGT'45'return_172 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelGT'45'return_172 ~v0 ~v1 ~v2 ~v3 v4
  = du_RelGT'45'return_172 v4
du_RelGT'45'return_172 ::
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelGT'45'return_172 v0
  = coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v0
-- Once.Adequacy.GradedRelation.RelGT-bind
d_RelGT'45'bind_192 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelGT'45'bind_192 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelGT'45'bind_192 v3 v4 v7 v8
du_RelGT'45'bind_192 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelGT'45'bind_192 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
      (coe v0) (coe v1) (coe v2) (coe (\ v4 v5 -> coe v3 v4 v5))
-- Once.Adequacy.GradedRelation.RelGᵖ-bind
d_RelG'7510''45'bind_232 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelG'7510''45'bind_232 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelG'7510''45'bind_232 v3 v4 v7 v8
du_RelG'7510''45'bind_232 ::
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelG'7510''45'bind_232 v0 v1 v2 v3
  = coe
      du_RelGT'45'bind_192
      (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v0) (coe v1)
      (coe v2) (coe v3)
-- Once.Adequacy.GradedRelation.RelGᵖᵉ-bind
d_RelG'7510''7497''45'bind_274 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelG'7510''7497''45'bind_274 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9
                               v10
  = du_RelG'7510''7497''45'bind_274 v5 v6 v9 v10
du_RelG'7510''7497''45'bind_274 ::
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelG'7510''7497''45'bind_274 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7 -> coe v3 v0 v4 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-bind
d_RelGM'45'bind_314 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelGM'45'bind_314 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_RelGM'45'bind_314 v1 v4 v5 v6
du_RelGM'45'bind_314 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelGM'45'bind_314 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe du_RelG'7510''45'bind_232 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe du_RelGT'45'bind_192 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-fmap
d_RelGM'45'fmap_370 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelGM'45'fmap_370 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 v8 v9
  = du_RelGM'45'fmap_370 v1 v4 v5 v6 v8 v9
du_RelGM'45'fmap_370 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelGM'45'fmap_370 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
             (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v1)) (coe v2)
             (coe (\ v6 v7 -> coe v5 v6 v7)) (coe v4)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
             (coe v1) (coe v2) (coe (\ v6 v7 -> coe v5 v6 v7)) (coe v4)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
             (coe v2)
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v3 v6)))
             (coe v4)
             (coe
                (\ v6 v7 v8 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                     (coe v3 v6) (coe v5 v6 v7 v8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-return
d_RelGM'45'return_416 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelGM'45'return_416 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_RelGM'45'return_416 v2 v4 v6
du_RelGM'45'return_416 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_RelGM'45'return_416 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
        -> coe du_RelGT'45'return_172 (coe v2)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
             v1 v2
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe du_RelGT'45'return_172 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.prjB-rel
d_prjB'45'rel_438 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prjB'45'rel_438 = erased
-- Once.Adequacy.GradedRelation.injB-rel
d_injB'45'rel_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB'45'rel_478 ~v0 v1 v2 v3 = du_injB'45'rel_478 v1 v2 v3
du_injB'45'rel_478 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_injB'45'rel_478 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14 -> erased
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16 -> erased
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_injB'45'rel_478 (coe v7) (coe v5) (coe v9))
                           (coe du_injB'45'rel_478 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_injB'45'rel_478 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_injB'45'rel_478 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embνᵃ-∼
d_embν'7491''45''8764'_512 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.ValueDomainLaws.T__'8764''7496'__12
d_embν'7491''45''8764'_512 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomainLaws.C_constructor_24
      (coe
         d_embLayer'7491'_520 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_204 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.embLayerᵃ
d_embLayer'7491'_520 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_embLayer'7491'_520 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554
                    (d_mapEmbν'7491''45''8764'_530
                       (coe v0) (coe v1) (coe v1) (coe v2) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbνᵃ-∼
d_mapEmbν'7491''45''8764'_530 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'7491''45''8764'_530 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'7491''45''8764'_512 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_530 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_530 (coe v0) (coe v1) (coe v7) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_mapEmbν'7491''45''8764'_530 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'7491''45''8764'_530 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-ret
d_RelGM'45'ret_598 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 -> AgdaAny
d_RelGM'45'ret_598 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_RelGM'45'ret_598 v2 v4 v6
du_RelGM'45'ret_598 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 -> AgdaAny
du_RelGM'45'ret_598 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10 -> coe v2
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v5
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                    v1 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
