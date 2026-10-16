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
import qualified MAlonzo.Code.Once.Denotation.GuardedLaws
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomainLaws
import qualified MAlonzo.Code.Once.Lang.Graded
import qualified MAlonzo.Code.Once.Lang.GradedOps
import qualified MAlonzo.Code.Once.Lang.Guarded
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
-- Once.Adequacy.GradedRelation._∼⁺ᵈ_
d__'8764''8314''7496'__34 a0 a1 a2 a3 = ()
data T__'8764''8314''7496'__34
  = C_constructor_46 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
-- Once.Adequacy.GradedRelation._∼⁺ᵈ_.force-∼⁺ᵈ
d_force'45''8764''8314''7496'_44 ::
  T__'8764''8314''7496'__34 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_force'45''8764''8314''7496'_44 v0
  = case coe v0 of
      C_constructor_46 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._∼∞ᵈ_
d__'8764''8734''7496'__54 a0 a1 a2 a3 = ()
data T__'8764''8734''7496'__54
  = C_constructor_66 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
-- Once.Adequacy.GradedRelation._∼∞ᵈ_.force-∼∞ᵈ
d_force'45''8764''8734''7496'_64 ::
  T__'8764''8734''7496'__54 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_force'45''8764''8734''7496'_64 v0
  = case coe v0 of
      C_constructor_66 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGV
d_RelGV_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_70 = erased
-- Once.Adequacy.GradedRelation.RelGT
d_RelGT_74 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGT_74 = erased
-- Once.Adequacy.GradedRelation.RelGM
d_RelGM_80 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGM_80 = erased
-- Once.Adequacy.GradedRelation.RelGT-return
d_RelGT'45'return_230 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_RelGT'45'return_230 ~v0 ~v1 ~v2 ~v3 v4
  = du_RelGT'45'return_230 v4
du_RelGT'45'return_230 ::
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelGT'45'return_230 v0
  = coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v0
-- Once.Adequacy.GradedRelation.RelGT-bind
d_RelGT'45'bind_250 ::
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
d_RelGT'45'bind_250 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelGT'45'bind_250 v3 v4 v7 v8
du_RelGT'45'bind_250 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelGT'45'bind_250 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
      (coe v0) (coe v1) (coe v2) (coe (\ v4 v5 -> coe v3 v4 v5))
-- Once.Adequacy.GradedRelation.RelGᵖ-bind
d_RelG'7510''45'bind_290 ::
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
d_RelG'7510''45'bind_290 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_RelG'7510''45'bind_290 v3 v4 v7 v8
du_RelG'7510''45'bind_290 ::
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542) ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_RelG'7510''45'bind_290 v0 v1 v2 v3
  = coe
      du_RelGT'45'bind_250
      (coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v0) (coe v1)
      (coe v2) (coe v3)
-- Once.Adequacy.GradedRelation.RelGᵖᵉ-bind
d_RelG'7510''7497''45'bind_332 ::
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
d_RelG'7510''7497''45'bind_332 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9
                               v10
  = du_RelG'7510''7497''45'bind_332 v5 v6 v9 v10
du_RelG'7510''7497''45'bind_332 ::
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelG'7510''7497''45'bind_332 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7 -> coe v3 v0 v4 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-bind
d_RelGM'45'bind_372 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelGM'45'bind_372 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelGM'45'bind_372 v1 v4 v5 v6 v7
du_RelGM'45'bind_372 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelGM'45'bind_372 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe du_RelG'7510''45'bind_290 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe du_RelGT'45'bind_250 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe
             (\ v5 v6 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45''8776'_694
                  (coe
                     MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                     (coe
                        MAlonzo.Code.Once.Lang.Graded.du_bindM_82 (coe v0) (coe v1)
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v2)
                     (coe v4))
                  (coe
                     MAlonzo.Code.Once.Denotation.GuardedLaws.du_forget'45'bind'8314'_14
                     (coe v1)
                     (coe
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v3 v7))))
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
                     (coe v2)
                     (coe
                        (\ v7 ->
                           coe MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v3 v7)))
                     (coe v5) (coe v6)))
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
             (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-fmap
d_RelGM'45'fmap_446 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_RelGM'45'fmap_446 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_RelGM'45'fmap_446 v1 v4 v5 v6 v7 v8 v9
du_RelGM'45'fmap_446 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_RelGM'45'fmap_446 v0 v1 v2 v3 v4 v5 v6
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
             (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v1)) (coe v2)
             (coe (\ v7 v8 -> coe v6 v7 v8)) (coe v5)
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
             (coe v1) (coe v2) (coe (\ v7 v8 -> coe v6 v7 v8)) (coe v5)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45''8776'_694
             (coe
                MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                (coe
                   MAlonzo.Code.Once.Lang.GradedOps.du_fmapM_76 (coe v0) (coe v3)
                   (coe v1)))
             (coe MAlonzo.Code.Once.Lang.Trace.du_fmapT_170 (coe v4) (coe v2))
             (coe
                MAlonzo.Code.Once.Denotation.GuardedLaws.du_forget'45'bind'8314'_14
                (coe v1)
                (coe
                   (\ v7 ->
                      coe
                        MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v3 v7))))
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
                (coe v2)
                (coe
                   (\ v7 ->
                      coe
                        MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v3 v7)))
                (coe v5)
                (coe
                   (\ v7 v8 v9 ->
                      coe
                        MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                        (coe v3 v7) (coe v6 v7 v8 v9))))
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_40
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelT'8734''8242''45'bind_596
             (coe v2)
             (coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v3 v7)))
             (coe v5)
             (coe
                (\ v7 v8 v9 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                     (coe v3 v7) (coe v6 v7 v8 v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-return
d_RelGM'45'return_510 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelGM'45'return_510 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_RelGM'45'return_510 v2 v4 v6
du_RelGM'45'return_510 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_RelGM'45'return_510 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
        -> coe du_RelGT'45'return_230 (coe v2)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
             v1 v2
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe du_RelGT'45'return_230 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.prjB-rel
d_prjB'45'rel_532 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prjB'45'rel_532 = erased
-- Once.Adequacy.GradedRelation.injB-rel
d_injB'45'rel_572 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB'45'rel_572 ~v0 v1 v2 v3 = du_injB'45'rel_572 v1 v2 v3
du_injB'45'rel_572 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_injB'45'rel_572 v0 v1 v2
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
                           (coe du_injB'45'rel_572 (coe v7) (coe v5) (coe v9))
                           (coe du_injB'45'rel_572 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_injB'45'rel_572 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_injB'45'rel_572 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embν-∼
d_embν'45''8764'_606 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  T__'8764''7510''7496'__14 -> T__'8764''8734''7496'__54
d_embν'45''8764'_606 v0 v1 v2 v3 v4
  = coe
      C_constructor_66
      (coe
         d_lay'7510'_614 (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.layᵖ
d_lay'7510'_614 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_lay'7510'_614 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                    (MAlonzo.Code.Once.Lang.GradedOps.d_mapEmbν_396
                       (coe v1) (coe v1)
                       (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_250 (coe v2)))
                    (d_mapEmbν'45''8764'_624
                       (coe v0) (coe v1) (coe v1)
                       (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_250 (coe v2))
                       (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbν-∼
d_mapEmbν'45''8764'_624 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'45''8764'_624 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'45''8764'_606 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'45''8764'_624 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'45''8764'_624 (coe v0) (coe v1) (coe v7) (coe v8)
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
                                     d_mapEmbν'45''8764'_624 (coe v0) (coe v1) (coe v6) (coe v8)
                                     (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'45''8764'_624 (coe v0) (coe v1) (coe v7) (coe v9)
                                     (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embνᵃ-∼
d_embν'7491''45''8764'_688 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Graded.T_ν'7510'_244 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.ValueDomainLaws.T__'8764''7496'__12
d_embν'7491''45''8764'_688 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomainLaws.C_constructor_24
      (coe
         d_embLayer'7491'_696 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Graded.d_force'7510'_250 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.embLayerᵃ
d_embLayer'7491'_696 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_embLayer'7491'_696 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554
                    (d_mapEmbν'7491''45''8764'_706
                       (coe v0) (coe v1) (coe v1) (coe v2) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbνᵃ-∼
d_mapEmbν'7491''45''8764'_706 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'7491''45''8764'_706 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'7491''45''8764'_688 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_706 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_706 (coe v0) (coe v1) (coe v7) (coe v8)
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
                                     d_mapEmbν'7491''45''8764'_706 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'7491''45''8764'_706 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embν∞ᵈ-∼
d_embν'8734''7496''45''8764'_770 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Denotation.ValueDomainLaws.T__'8764''7496'__12 ->
  T__'8764''8734''7496'__54
d_embν'8734''7496''45''8764'_770 v0 v1 v2 v3 v4
  = coe
      C_constructor_66
      (coe
         d_embLay'8734''45''8764'_778 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomainLaws.d_force'45''8764'_22
            (coe v4)))
-- Once.Adequacy.GradedRelation.embLay∞-∼
d_embLay'8734''45''8764'_778 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_embLay'8734''45''8764'_778 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v8
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Trace.C_ret_114 v9
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                           (MAlonzo.Code.Once.Lang.GradedOps.d_mapEmbν'8734''7496'_500
                              (coe v1) (coe v1) (coe v8))
                           (d_mapEmbν'8734''7496''45''8764'_788
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
                              MAlonzo.Code.Once.Lang.GradedOps.d_embLay'8734'_494
                                (coe v1) (coe v12 v16))
                           (\ v16 ->
                              d_embLay'8734''45''8764'_778
                                (coe v0) (coe v1) (coe v12 v16) (coe v15 v16) (coe v9 v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbν∞ᵈ-∼
d_mapEmbν'8734''7496''45''8764'_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'8734''7496''45''8764'_788 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'8734''7496''45''8764'_770 (coe v0) (coe v1) (coe v3)
             (coe v4) (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'8734''7496''45''8764'_788 (coe v0) (coe v1) (coe v6)
                           (coe v8) (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'8734''7496''45''8764'_788 (coe v0) (coe v1) (coe v7)
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
                                     d_mapEmbν'8734''7496''45''8764'_788 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'8734''7496''45''8764'_788 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embν⁺-∼
d_embν'8314''45''8764'_860 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Guarded.T_ν'8314'_164 ->
  MAlonzo.Code.Once.Lang.Stream.T_ν'7496'_14 ->
  T__'8764''8314''7496'__34 -> T__'8764''8734''7496'__54
d_embν'8314''45''8764'_860 v0 v1 v2 v3 v4
  = coe
      C_constructor_66
      (coe
         d_embRoot'8314''45''8764'_868 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Guarded.d_force'8314'_170 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Stream.d_force'7496'_20 (coe v3))
         (coe d_force'45''8764''8314''7496'_44 (coe v4)))
-- Once.Adequacy.GradedRelation.embRoot⁺-∼
d_embRoot'8314''45''8764'_868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_embRoot'8314''45''8764'_868 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64 v5 v6 v7
        -> case coe v4 of
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532 v11 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Lang.Trace.C_call_118 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532
                           (\ v18 ->
                              MAlonzo.Code.Once.Lang.GradedOps.d_embTree'8314'_670
                                (coe v1) (coe v7 v18))
                           (\ v18 ->
                              coe
                                du_embTree'8314''45''8764'_876 (coe v0) (coe v1) (coe v17 v18)
                                (coe v14 v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Guarded.C_halt'8314'_68 v5 v6
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embTree⁺-∼
d_embTree'8314''45''8764'_876 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
d_embTree'8314''45''8764'_876 v0 v1 ~v2 v3 v4
  = du_embTree'8314''45''8764'_876 v0 v1 v3 v4
du_embTree'8314''45''8764'_876 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelT'8734''8242'_504
du_embTree'8314''45''8764'_876 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518 v5 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v9
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'ret_518
                    (MAlonzo.Code.Once.Lang.GradedOps.d_mapEmbν'8314'_680
                       (coe v1) (coe v1) (coe v5))
                    (d_mapEmbν'8314''45''8764'_886
                       (coe v0) (coe v1) (coe v1) (coe v5) (coe v9) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532 v7 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'call_532
                    (\ v14 ->
                       MAlonzo.Code.Once.Lang.GradedOps.d_embTree'8314'_670
                         (coe v1) (coe v7 v14))
                    (\ v14 ->
                       coe
                         du_embTree'8314''45''8764'_876 (coe v0) (coe v1) (coe v13 v14)
                         (coe v10 v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbν⁺-∼
d_mapEmbν'8314''45''8764'_886 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'8314''45''8764'_886 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe
             d_embν'8314''45''8764'_860 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'8314''45''8764'_886 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'8314''45''8764'_886 (coe v0) (coe v1) (coe v7) (coe v8)
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
                                     d_mapEmbν'8314''45''8764'_886 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'8314''45''8764'_886 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-ret
d_RelGM'45'ret_1016 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 -> AgdaAny
d_RelGM'45'ret_1016 ~v0 ~v1 v2 ~v3 v4 ~v5 v6
  = du_RelGM'45'ret_1016 v2 v4 v6
du_RelGM'45'ret_1016 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 -> AgdaAny
du_RelGM'45'ret_1016 v0 v1 v2
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
