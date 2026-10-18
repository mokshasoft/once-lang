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
import qualified MAlonzo.Code.Once.Lang.GradedOps
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
-- Once.Adequacy.GradedRelation._∼∞ᵈ_
d__'8764''8734''7496'__34 a0 a1 a2 a3 = ()
data T__'8764''8734''7496'__34
  = C_constructor_46 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
-- Once.Adequacy.GradedRelation._∼∞ᵈ_.force-∼∞ᵈ
d_force'45''8764''8734''7496'_44 ::
  T__'8764''8734''7496'__34 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_force'45''8764''8734''7496'_44 v0
  = case coe v0 of
      C_constructor_46 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGV
d_RelGV_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_50 = erased
-- Once.Adequacy.GradedRelation.RelGT
d_RelGT_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGT_54 = erased
-- Once.Adequacy.GradedRelation.RelGM
d_RelGM_60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGM_60 = erased
-- Once.Adequacy.GradedRelation.RelGT-return
d_RelGT'45'return_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelGT'45'return_198 ~v0 ~v1 ~v2 ~v3 v4
  = du_RelGT'45'return_198 v4
du_RelGT'45'return_198 ::
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelGT'45'return_198 v0
  = coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v0
-- Once.Adequacy.GradedRelation.RelGT-bind
d_RelGT'45'bind_218 ::
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
d_RelGT'45'bind_218 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelGT'45'bind_218 v3 v4 v7 v8
du_RelGT'45'bind_218 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelGT'45'bind_218 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
      (coe v0) (coe v1) (coe v2) (coe (\ v4 v5 -> coe v3 v4 v5))
-- Once.Adequacy.GradedRelation.RelGᵖ-bind
d_RelG'7510''45'bind_258 ::
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
d_RelG'7510''45'bind_258 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelG'7510''45'bind_258 v3 v4 v7 v8
du_RelG'7510''45'bind_258 ::
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelG'7510''45'bind_258 v0 v1 v2 v3
  = coe
      du_RelGT'45'bind_218
      (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v0) (coe v1)
      (coe v2) (coe v3)
-- Once.Adequacy.GradedRelation.RelGᵖᵉ-bind
d_RelG'7510''7497''45'bind_300 ::
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
d_RelG'7510''7497''45'bind_300 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9
                               v10
  = du_RelG'7510''7497''45'bind_300 v5 v6 v9 v10
du_RelG'7510''7497''45'bind_300 ::
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelG'7510''7497''45'bind_300 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7 -> coe v3 v0 v4 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-bind
d_RelGM'45'bind_340 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelGM'45'bind_340 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7
  = du_RelGM'45'bind_340 v1 v4 v5 v6
du_RelGM'45'bind_340 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelGM'45'bind_340 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe du_RelG'7510''45'bind_258 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe du_RelGT'45'bind_218 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-fmap
d_RelGM'45'fmap_396 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelGM'45'fmap_396 ~v0 v1 ~v2 ~v3 v4 v5 v6 ~v7 v8 v9
  = du_RelGM'45'fmap_396 v1 v4 v5 v6 v8 v9
du_RelGM'45'fmap_396 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelGM'45'fmap_396 v0 v1 v2 v3 v4 v5
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
d_RelGM'45'return_442 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelGM'45'return_442 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_RelGM'45'return_442 v2 v4 v6
du_RelGM'45'return_442 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_RelGM'45'return_442 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
        -> coe du_RelGT'45'return_198 (coe v2)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
             v1 v2
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe du_RelGT'45'return_198 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.prjB-rel
d_prjB'45'rel_464 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prjB'45'rel_464 = erased
-- Once.Adequacy.GradedRelation.injB-rel
d_injB'45'rel_504 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB'45'rel_504 ~v0 v1 v2 v3 = du_injB'45'rel_504 v1 v2 v3
du_injB'45'rel_504 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_injB'45'rel_504 v0 v1 v2
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
                           (coe du_injB'45'rel_504 (coe v7) (coe v5) (coe v9))
                           (coe du_injB'45'rel_504 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_injB'45'rel_504 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_injB'45'rel_504 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embν-∼
d_embν'45''8764'_538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  T__'8764''7510''7496'__14 -> T__'8764''8734''7496'__34
d_embν'45''8764'_538 v0 v1 v2 v3 v4
  = coe
      C_constructor_46
      (coe
         d_lay'7510'_546 (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.layᵖ
d_lay'7510'_546 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_lay'7510'_546 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                    (MAlonzo.Code.Once.Lang.GradedOps.d_mapEmbν_392
                       (coe v1) (coe v1)
                       (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_204 (coe v2)))
                    (d_mapEmbν'45''8764'_556
                       (coe v0) (coe v1) (coe v1)
                       (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_204 (coe v2))
                       (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbν-∼
d_mapEmbν'45''8764'_556 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'45''8764'_556 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'45''8764'_538 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'45''8764'_556 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'45''8764'_556 (coe v0) (coe v1) (coe v7) (coe v8)
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
                                     d_mapEmbν'45''8764'_556 (coe v0) (coe v1) (coe v6) (coe v8)
                                     (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'45''8764'_556 (coe v0) (coe v1) (coe v7) (coe v9)
                                     (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embνᵃ-∼
d_embν'7491''45''8764'_620 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.ValueDomainLaws.T__'8764''7496'__12
d_embν'7491''45''8764'_620 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomainLaws.C_constructor_24
      (coe
         d_embLayer'7491'_628 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_204 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.embLayerᵃ
d_embLayer'7491'_628 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_embLayer'7491'_628 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554
                    (d_mapEmbν'7491''45''8764'_638
                       (coe v0) (coe v1) (coe v1) (coe v2) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbνᵃ-∼
d_mapEmbν'7491''45''8764'_638 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'7491''45''8764'_638 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'7491''45''8764'_620 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_638 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_638 (coe v0) (coe v1) (coe v7) (coe v8)
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
                                     d_mapEmbν'7491''45''8764'_638 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'7491''45''8764'_638 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embν∞ᵈ-∼
d_embν'8734''7496''45''8764'_702 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Denotation.ValueDomainLaws.T__'8764''7496'__12 ->
  T__'8764''8734''7496'__34
d_embν'8734''7496''45''8764'_702 v0 v1 v2 v3 v4
  = coe
      C_constructor_46
      (coe
         d_embLay'8734''45''8764'_710 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomainLaws.d_force'45''8764'_22
            (coe v4)))
-- Once.Adequacy.GradedRelation.embLay∞-∼
d_embLay'8734''45''8764'_710 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_embLay'8734''45''8764'_710 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114 v9
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                           (MAlonzo.Code.Once.Lang.GradedOps.d_mapEmbν'8734''7496'_496
                              (coe v1) (coe v1) (coe v8))
                           (d_mapEmbν'8734''7496''45''8764'_720
                              (coe v0) (coe v1) (coe v1) (coe v8) (coe v9) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'call_566 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v10 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Trace.C_call_118 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532
                           (\ v16 ->
                              MAlonzo.Code.Once.Lang.GradedOps.d_embLay'8734'_490
                                (coe v1) (coe v12 v16))
                           (\ v16 ->
                              d_embLay'8734''45''8764'_710
                                (coe v0) (coe v1) (coe v12 v16) (coe v15 v16) (coe v9 v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbν∞ᵈ-∼
d_mapEmbν'8734''7496''45''8764'_720 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'8734''7496''45''8764'_720 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'8734''7496''45''8764'_702 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'8734''7496''45''8764'_720 (coe v0) (coe v1) (coe v6)
                           (coe v8) (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'8734''7496''45''8764'_720 (coe v0) (coe v1) (coe v7)
                           (coe v8) (coe v9) (coe v5)
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
                                     d_mapEmbν'8734''7496''45''8764'_720 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'8734''7496''45''8764'_720 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-ret
d_RelGM'45'ret_796 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 -> AgdaAny
d_RelGM'45'ret_796 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_RelGM'45'ret_796 v2 v4 v6
du_RelGM'45'ret_796 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 -> AgdaAny
du_RelGM'45'ret_796 v0 v1 v2
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
