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
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Denotation.ValueRelPER
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Graded
import qualified MAlonzo.Code.Once.Internal.GradedOps
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Stream
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.GradedRelation._∼ᵖᵈ_
d__'8764''7510''7496'__14 a0 a1 a2 a3 = ()
data T__'8764''7510''7496'__14
  = C_constructor_26 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
-- Once.Adequacy.GradedRelation._∼ᵖᵈ_.force-∼ᵖᵈ
d_force'45''8764''7510''7496'_24 ::
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_force'45''8764''7510''7496'_24 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._∼ᵈ_
d__'8764''7496'__34 a0 a1 a2 a3 = ()
data T__'8764''7496'__34
  = C_constructor_46 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
-- Once.Adequacy.GradedRelation._∼ᵈ_.force-∼
d_force'45''8764'_44 ::
  T__'8764''7496'__34 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_force'45''8764'_44 v0
  = case coe v0 of
      C_constructor_46 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGV
d_RelGV_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> ()
d_RelGV_50 = erased
-- Once.Adequacy.GradedRelation.RelGM
d_RelGM_56 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()
d_RelGM_56 = erased
-- Once.Adequacy.GradedRelation.RelGT
d_RelGT_68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()
d_RelGT_68 = erased
-- Once.Adequacy.GradedRelation.sameˡ
d_same'737'_188 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_same'737'_188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_same'737'_188 v8
du_same'737'_188 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_same'737'_188 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
         (coe v0))
-- Once.Adequacy.GradedRelation.ret≈ˡ
d_ret'8776''737'_202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
d_ret'8776''737'_202 ~v0 ~v1 ~v2 ~v3 v4 = du_ret'8776''737'_202 v4
du_ret'8776''737'_202 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
du_ret'8776''737'_202 v0
  = coe
      MAlonzo.Code.Once.Internal.Iterative.C_constructor_348
      (coe
         MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276
         (coe MAlonzo.Code.Once.Internal.Iterative.C_done'8776'_318 v0))
-- Once.Adequacy.GradedRelation.RelGT-return
d_RelGT'45'return_212 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelGT'45'return_212 ~v0 ~v1 ~v2 ~v3 v4
  = du_RelGT'45'return_212 v4
du_RelGT'45'return_212 ::
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelGT'45'return_212 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v0)
-- Once.Adequacy.GradedRelation.RelGT-bind
d_RelGT'45'bind_232 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelGT'45'bind_232 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_RelGT'45'bind_232 v3 v4 v5 v6 v7 v8
du_RelGT'45'bind_232 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelGT'45'bind_232 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
      (coe
         MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
         (coe
            MAlonzo.Code.Once.Internal.Trace.du__'62''62''61'T__132 (coe v0)
            (coe v2)))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v0))
         (coe
            (\ v6 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v2 v6))))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
         (coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v0))
         (coe v1)
         (coe
            (\ v6 ->
               coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v2 v6)))
         (coe v3) (coe v4) (coe v5))
-- Once.Adequacy.GradedRelation.RelGᵖ-bind
d_RelG'7510''45'bind_266 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelG'7510''45'bind_266 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_RelG'7510''45'bind_266 v3 v4 v5 v6 v7 v8
du_RelG'7510''45'bind_266 ::
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelG'7510''45'bind_266 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
      (coe
         MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         (coe
            MAlonzo.Code.Once.Internal.Graded.du__'62''62''61''7510'__68
            (coe v0) (coe v2)))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
         (coe v2 v0))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe v1) (coe v3))
      (coe du_ret'8776''737'_202 erased)
      (coe
         du_same'737'_188
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
            (coe
               MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146
               (coe
                  MAlonzo.Code.Once.Spec.Grade.C_fin_42
                  (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
               (coe v0))
            (coe v1)
            (coe
               (\ v6 ->
                  coe
                    MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_fin_42
                       (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                    (coe v2 v6)))
            (coe v3) (coe v4) (coe v5)))
-- Once.Adequacy.GradedRelation.RelGᵖᵉ-bind
d_RelG'7510''7497''45'bind_310 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> AgdaAny) ->
  AgdaAny
d_RelG'7510''7497''45'bind_310 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
                               v10 v11
  = du_RelG'7510''7497''45'bind_310 v5 v6 v7 v8 v9 v10 v11
du_RelG'7510''7497''45'bind_310 ::
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> AgdaAny) ->
  AgdaAny
du_RelG'7510''7497''45'bind_310 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_go_338 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
      (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
         (coe v4))
-- Once.Adequacy.GradedRelation._.go
d_go_338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  AgdaAny
d_go_338 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11 v12 ~v13 v14
  = du_go_338 v5 v6 v7 v8 v10 v11 v12 v14
du_go_338 ::
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  AgdaAny
du_go_338 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe
                           v5
                           (coe
                              MAlonzo.Code.Once.Internal.Graded.du__'62''62''61''7510'__68
                              (coe v0) (coe v2))
                           (coe
                              MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                              (coe v1) (coe v3))
                           (coe v3 v12) erased (coe v4 v0 v12 v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-bind
d_RelGM'45'bind_368 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelGM'45'bind_368 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelGM'45'bind_368 v1 v4 v5 v6 v7
du_RelGM'45'bind_368 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelGM'45'bind_368 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v5
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    du_RelG'7510''45'bind_266 (coe v1) (coe v2) (coe v3) (coe v4)
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe du_RelGT'45'bind_232 (coe v1) (coe v2) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             (\ v5 v6 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                  (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGM-fmap
d_RelGM'45'fmap_416 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelGM'45'fmap_416 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_RelGM'45'fmap_416 v1 v4 v5 v6 v7 v8 v9
du_RelGM'45'fmap_416 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelGM'45'fmap_416 v0 v1 v2 v3 v4 v5 v6
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
        -> case coe v7 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    du_same'737'_188
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                       (coe
                          MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146 (coe v0)
                          (coe v1))
                       (coe v2)
                       (coe
                          (\ v8 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                               (coe v3 v8)))
                       (coe
                          (\ v8 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                               (coe v4 v8)))
                       (coe v5)
                       (coe
                          (\ v8 v9 v10 ->
                             coe
                               MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                               (coe v6 v8 v9 v10))))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
                    (coe
                       MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.GradedOps.du_fmapM_76 (coe v0) (coe v3)
                          (coe v1)))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v1))
                       (coe
                          (\ v8 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                               (coe MAlonzo.Code.Once.Internal.Trace.C_ret_114 (coe v3 v8)))))
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358 (coe v4)
                       (coe v2))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
                       (coe v1)
                       (coe
                          (\ v8 ->
                             coe MAlonzo.Code.Once.Internal.Trace.C_ret_114 (coe v3 v8))))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                       (coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v1))
                       (coe v2)
                       (coe
                          (\ v8 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                               (coe MAlonzo.Code.Once.Internal.Trace.C_ret_114 (coe v3 v8))))
                       (coe
                          (\ v8 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                               (coe v4 v8)))
                       (coe v5)
                       (coe (\ v8 v9 v10 -> coe du_embed'45'ret_450 (coe v6 v8 v9 v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
             (coe v1) (coe v2)
             (coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                     (coe v3 v7)))
             (coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                     (coe v4 v7)))
             (coe v5)
             (coe
                (\ v7 v8 v9 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe v6 v7 v8 v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.embed-ret
d_embed'45'ret_450 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_embed'45'ret_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_embed'45'ret_450 v11
du_embed'45'ret_450 ::
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_embed'45'ret_450 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v0)
-- Once.Adequacy.GradedRelation.RelGM-return
d_RelGM'45'return_474 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelGM'45'return_474 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_RelGM'45'return_474 v2 v6
du_RelGM'45'return_474 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelGM'45'return_474 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe v1)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe du_RelGT'45'return_212 (coe v1)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.prjB-rel
d_prjB'45'rel_492 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prjB'45'rel_492 = erased
-- Once.Adequacy.GradedRelation.injB-rel
d_injB'45'rel_532 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_injB'45'rel_532 ~v0 v1 v2 v3 = du_injB'45'rel_532 v1 v2 v3
du_injB'45'rel_532 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
du_injB'45'rel_532 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Unit_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Int_14
        -> erased
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Float_16
        -> erased
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_injB'45'rel_532 (coe v7) (coe v5) (coe v9))
                           (coe du_injB'45'rel_532 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_injB'45'rel_532 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_injB'45'rel_532 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.embνᵃ-∼
d_embν'7491''45''8764'_566 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  T__'8764''7510''7496'__14 -> T__'8764''7496'__34
d_embν'7491''45''8764'_566 v0 v1 v2 v3 v4
  = coe
      C_constructor_46
      (coe
         d_embLayer'7491'_574 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Graded.d_force'7510'_204 (coe v2))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation.embLayerᵃ
d_embLayer'7491'_574 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_embLayer'7491'_574 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_embLayerB'7491'_582 (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v4)))
-- Once.Adequacy.GradedRelation.embLayerBᵃ
d_embLayerB'7491'_582 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_embLayerB'7491'_582 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                           (d_mapEmbν'7491''45''8764'_592
                              (coe v0) (coe v1) (coe v1) (coe v2) (coe v9) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.mapEmbνᵃ-∼
d_mapEmbν'7491''45''8764'_592 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapEmbν'7491''45''8764'_592 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> coe v5
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             d_embν'7491''45''8764'_566 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_592 (coe v0) (coe v1) (coe v6) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_mapEmbν'7491''45''8764'_592 (coe v0) (coe v1) (coe v7) (coe v8)
                           (coe v9) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_mapEmbν'7491''45''8764'_592 (coe v0) (coe v1) (coe v6)
                                     (coe v8) (coe v10) (coe v12))
                                  (coe
                                     d_mapEmbν'7491''45''8764'_592 (coe v0) (coe v1) (coe v7)
                                     (coe v9) (coe v11) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelS-embed-fmap
d_RelS'45'embed'45'fmap_672 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'embed'45'fmap_672 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_RelS'45'embed'45'fmap_672 v0 v4 v6 v7 v8
du_RelS'45'embed'45'fmap_672 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'embed'45'fmap_672 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45''8776''737'_794
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du_embed_136
         (coe
            MAlonzo.Code.Once.Internal.Trace.du_fmapT_170 (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v2))
         (coe
            (\ v5 ->
               coe
                 MAlonzo.Code.Once.Internal.Iterative.du_embed_136
                 (coe MAlonzo.Code.Once.Internal.Trace.C_ret_114 (coe v1 v5)))))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_embed'45'bind_900
         (coe v2)
         (coe
            (\ v5 ->
               coe MAlonzo.Code.Once.Internal.Trace.C_ret_114 (coe v1 v5))))
      (coe
         du_emb'45'fmap_696 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Once.Internal.Iterative.du_embed_136 (coe v2))
         (coe v3) (coe v4))
-- Once.Adequacy.GradedRelation._.emb-fmap
d_emb'45'fmap_696 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_emb'45'fmap_696 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11 v12
  = du_emb'45'fmap_696 v0 v4 v6 v7 v8 v10 v11 v12
du_emb'45'fmap_696 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_emb'45'fmap_696 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_emb'45'fmapB_710 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v5))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v6))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v7)))
-- Once.Adequacy.GradedRelation._.emb-fmapB
d_emb'45'fmapB_710 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_emb'45'fmapB_710 v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 ~v9 v10 v11 v12
  = du_emb'45'fmapB_710 v0 v4 v6 v7 v8 v10 v11 v12
du_emb'45'fmapB_710 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_emb'45'fmapB_710 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v10
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v10
        -> case coe v5 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> case coe v6 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_emb'45'fmap_696 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v4) (coe v12) (coe v14) (coe v10))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
               -> case coe v6 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v19 ->
                              coe
                                du_emb'45'fmapB_710 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v15 v19) (coe v18 v19) (coe v12 v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.RelGᵖ-app
d_RelG'7510''45'app_740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelG'7510''45'app_740 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_RelG'7510''45'app_740 v3 v4 v5 v6 v7 v8
du_RelG'7510''45'app_740 ::
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelG'7510''45'app_740 v0 v1 v2 v3 v4 v5
  = coe
      du_RelG'7510''45'bind_266 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
-- Once.Adequacy.GradedRelation.RelGM-ret
d_RelGM'45'ret_770 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelGM'45'ret_770 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6
  = du_RelGM'45'ret_770 v2 v6
du_RelGM'45'ret_770 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelGM'45'ret_770 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52 -> coe v1
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe du_same'737'_188 (coe v1)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.pd-self
d_pd'45'self_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
d_pd'45'self_788 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.C_constructor_34
      (coe
         d_pd'45'run_794 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
            (coe MAlonzo.Code.Once.Internal.Graded.d_force'7510'_204 (coe v2)))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe d_force'45''8764''7510''7496'_24 (coe v4)))
-- Once.Adequacy.GradedRelation._.pd-run
d_pd'45'run_794 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_pd'45'run_794 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_pd'45'block_800 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v4)))
-- Once.Adequacy.GradedRelation._.pd-block
d_pd'45'block_800 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_pd'45'block_800 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (d_pd'45'layer_808
                                            (coe v0) (coe v1) (coe v1) (coe v9) (coe v11) (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (d_pd'45'run_794
                                            (coe v0) (coe v1) (coe v9) (coe v11) (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v16 ->
                              d_pd'45'block_800
                                (coe v0) (coe v1) (coe v12 v16) (coe v15 v16) (coe v9 v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.pd-layer
d_pd'45'layer_808 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_pd'45'layer_808 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             d_pd'45'self_788 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_pd'45'layer_808 (coe v0) (coe v1) (coe v6) (coe v8) (coe v9)
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_pd'45'layer_808 (coe v0) (coe v1) (coe v7) (coe v8) (coe v9)
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_pd'45'layer_808 (coe v0) (coe v1) (coe v6) (coe v8) (coe v10)
                                     (coe v12))
                                  (coe
                                     d_pd'45'layer_808 (coe v0) (coe v1) (coe v7) (coe v9) (coe v11)
                                     (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.ad-self
d_ad'45'self_860 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  T__'8764''7496'__34 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
d_ad'45'self_860 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.C_constructor_34
      (coe
         d_ad'45'run_866 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_embed_136
            (coe MAlonzo.Code.Once.Internal.Stream.d_force'7496'_20 (coe v2)))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe d_force'45''8764'_44 (coe v4)))
-- Once.Adequacy.GradedRelation._.ad-run
d_ad'45'run_866 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ad'45'run_866 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_ad'45'block_872 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v4)))
-- Once.Adequacy.GradedRelation._.ad-block
d_ad'45'block_872 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_ad'45'block_872 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (d_ad'45'layer_880
                                            (coe v0) (coe v1) (coe v1) (coe v9) (coe v11) (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (d_ad'45'run_866
                                            (coe v0) (coe v1) (coe v9) (coe v11) (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v16 ->
                              d_ad'45'block_872
                                (coe v0) (coe v1) (coe v12 v16) (coe v15 v16) (coe v9 v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.ad-layer
d_ad'45'layer_880 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_ad'45'layer_880 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             d_ad'45'self_860 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           d_ad'45'layer_880 (coe v0) (coe v1) (coe v6) (coe v8) (coe v9)
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           d_ad'45'layer_880 (coe v0) (coe v1) (coe v7) (coe v8) (coe v9)
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_ad'45'layer_880 (coe v0) (coe v1) (coe v6) (coe v8) (coe v10)
                                     (coe v12))
                                  (coe
                                     d_ad'45'layer_880 (coe v0) (coe v1) (coe v7) (coe v9) (coe v11)
                                     (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.pd-D
d_pd'45'D_934 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Graded.T_ν'7510'_198 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  T__'8764''7510''7496'__14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  T__'8764''7510''7496'__14
d_pd'45'D_934 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_26
      (coe
         d_pd'45'D'45'run_942 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
            (coe MAlonzo.Code.Once.Internal.Graded.d_force'7510'_204 (coe v2)))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v4))
         (coe d_force'45''8764''7510''7496'_24 (coe v5))
         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v6)))
-- Once.Adequacy.GradedRelation._.pd-D-run
d_pd'45'D'45'run_942 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_pd'45'D'45'run_942 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_pd'45'D'45'block_950 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v6)))
-- Once.Adequacy.GradedRelation._.pd-D-block
d_pd'45'D'45'block_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_pd'45'D'45'block_950 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                    -> case coe v6 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v16
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v17
                                                  -> case coe v17 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                                              (d_pd'45'D'45'layer_960
                                                                 (coe v0) (coe v1) (coe v1)
                                                                 (coe v11) (coe v13) (coe v18)
                                                                 (coe v9) (coe v16))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> case coe v6 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v16
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v17
                                                  -> case coe v17 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                                              (d_pd'45'D'45'run_942
                                                                 (coe v0) (coe v1) (coe v11)
                                                                 (coe v13) (coe v18) (coe v9)
                                                                 (coe v16))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> case coe v6 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v22
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v23 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                                         (\ v26 ->
                                            d_pd'45'D'45'block_950
                                              (coe v0) (coe v1) (coe v14 v26) (coe v17 v26)
                                              (coe v25 v26) (coe v11 v26) (coe v22 v26))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.pd-D-layer
d_pd'45'D'45'layer_960 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_pd'45'D'45'layer_960 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             d_pd'45'D_934 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe v7)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  d_pd'45'D'45'layer_960 (coe v0) (coe v1) (coe v8) (coe v10)
                                  (coe v11) (coe v12) (coe v6) (coe v7)
                           _ -> erased
                    _ -> erased
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  d_pd'45'D'45'layer_960 (coe v0) (coe v1) (coe v9) (coe v10)
                                  (coe v11) (coe v12) (coe v6) (coe v7)
                           _ -> erased
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                    -> case coe v7 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_pd'45'D'45'layer_960 (coe v0) (coe v1) (coe v8)
                                                   (coe v10) (coe v12) (coe v14) (coe v16)
                                                   (coe v18))
                                                (coe
                                                   d_pd'45'D'45'layer_960 (coe v0) (coe v1) (coe v9)
                                                   (coe v11) (coe v13) (coe v15) (coe v17)
                                                   (coe v19))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.ad-D
d_ad'45'D_1044 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Stream.T_ν'7496'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  T__'8764''7496'__34 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  T__'8764''7496'__34
d_ad'45'D_1044 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_46
      (coe
         d_ad'45'D'45'run_1052 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du_embed_136
            (coe MAlonzo.Code.Once.Internal.Stream.d_force'7496'_20 (coe v2)))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v4))
         (coe d_force'45''8764'_44 (coe v5))
         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v6)))
-- Once.Adequacy.GradedRelation._.ad-D-run
d_ad'45'D'45'run_1052 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_ad'45'D'45'run_1052 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_ad'45'D'45'block_1060 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v6)))
-- Once.Adequacy.GradedRelation._.ad-D-block
d_ad'45'D'45'block_1060 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_ad'45'D'45'block_1060 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                    -> case coe v6 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v16
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v17
                                                  -> case coe v17 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                                              (d_ad'45'D'45'layer_1070
                                                                 (coe v0) (coe v1) (coe v1)
                                                                 (coe v11) (coe v13) (coe v18)
                                                                 (coe v9) (coe v16))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> case coe v6 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v16
                                           -> case coe v4 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v17
                                                  -> case coe v17 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                                              (d_ad'45'D'45'run_1052
                                                                 (coe v0) (coe v1) (coe v11)
                                                                 (coe v13) (coe v18) (coe v9)
                                                                 (coe v16))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> case coe v6 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v22
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v23 v24 v25
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                                         (\ v26 ->
                                            d_ad'45'D'45'block_1060
                                              (coe v0) (coe v1) (coe v14 v26) (coe v17 v26)
                                              (coe v25 v26) (coe v11 v26) (coe v22 v26))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation._.ad-D-layer
d_ad'45'D'45'layer_1070 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_ad'45'D'45'layer_1070 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             d_ad'45'D_1044 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  d_ad'45'D'45'layer_1070 (coe v0) (coe v1) (coe v8) (coe v10)
                                  (coe v11) (coe v12) (coe v6) (coe v7)
                           _ -> erased
                    _ -> erased
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  d_ad'45'D'45'layer_1070 (coe v0) (coe v1) (coe v9) (coe v10)
                                  (coe v11) (coe v12) (coe v6) (coe v7)
                           _ -> erased
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                    -> case coe v7 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_ad'45'D'45'layer_1070 (coe v0) (coe v1)
                                                   (coe v8) (coe v10) (coe v12) (coe v14) (coe v16)
                                                   (coe v18))
                                                (coe
                                                   d_ad'45'D'45'layer_1070 (coe v0) (coe v1)
                                                   (coe v9) (coe v11) (coe v13) (coe v15) (coe v17)
                                                   (coe v19))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.right-self
d_right'45'self_1154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_right'45'self_1154 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe (\ v4 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           (\ v10 ->
                              case coe v10 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe d_right'45'self_1154 v0 v4 v6 v8 v11)
                                       (coe d_right'45'self_1154 v0 v5 v7 v9 v12)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe (\ v8 -> coe d_right'45'self_1154 v0 v4 v6 v7 v8)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe (\ v8 -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe (\ v8 -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe (\ v8 -> coe d_right'45'self_1154 v0 v5 v6 v7 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           (\ v9 ->
                              case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11 -> coe v11
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           (\ v9 ->
                              case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                  -> coe (\ v12 v13 -> coe v11 v12 v13)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           (\ v9 ->
                              case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                  -> coe (\ v12 v13 -> coe v11 v12 v13)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v4 -> erased
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    (\ v6 ->
                       d_pd'45'self_788
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
                            (coe v4))
                         (coe v2) (coe v3) (coe v6))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    (\ v6 ->
                       d_ad'45'self_860
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
                            (coe v4))
                         (coe v2) (coe v3) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_Int_34 -> erased
      MAlonzo.Code.Once.Internal.Type.C_Float_36 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.GV-D
d_GV'45'D_1234 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_GV'45'D_1234 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe (\ v5 v6 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  (\ v13 ->
                                     case coe v13 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                         -> coe
                                              (\ v16 ->
                                                 case coe v16 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             d_GV'45'D_1234 v0 v5 v7 v9 v11 v14 v17)
                                                          (coe
                                                             d_GV'45'D_1234 v0 v6 v8 v10 v12 v15
                                                             v18)
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> case coe v4 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                             -> coe (\ v10 v11 -> coe d_GV'45'D_1234 v0 v5 v7 v8 v9 v10 v11)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                             -> coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> coe (\ v9 -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> coe (\ v9 -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v4 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                             -> coe (\ v10 v11 -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                             -> coe (\ v10 v11 -> coe d_GV'45'D_1234 v0 v6 v7 v8 v9 v10 v11)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v5 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           (\ v10 ->
                              case coe v10 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                  -> coe
                                       (\ v13 ->
                                          coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               d_GM'45'D_1246 (coe v0) (coe v9) (coe v7)
                                               (coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                               (coe v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                               (coe v4 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                               (coe v11) (coe v13))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'leftself_718
                                               (coe v1)
                                               (coe
                                                  (\ v14 ->
                                                     coe
                                                       v4
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                               (coe
                                                  (\ v14 ->
                                                     coe
                                                       v3
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                               (coe v13)))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           (\ v10 ->
                              case coe v10 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                  -> coe
                                       (\ v13 ->
                                          coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               (\ v14 v15 v16 ->
                                                  d_GM'45'D_1246
                                                    (coe v0) (coe v9) (coe v7) (coe v2 v14)
                                                    (coe v3 v15) (coe v4 v15) (coe v11 v14 v15 v16)
                                                    (coe
                                                       v13 v15 v15
                                                       (coe
                                                          d_right'45'self_1154 v0 v5 v14 v15 v16))))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'leftself_718
                                               (coe v1) (coe v4) (coe v3) (coe v13)))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           (\ v10 ->
                              case coe v10 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                  -> coe
                                       (\ v13 ->
                                          coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               (\ v14 v15 v16 ->
                                                  d_GM'45'D_1246
                                                    (coe v0) (coe v9) (coe v7) (coe v2 v14)
                                                    (coe v3 v15) (coe v4 v15) (coe v11 v14 v15 v16)
                                                    (coe
                                                       v13 v15 v15
                                                       (coe
                                                          d_right'45'self_1154 v0 v5 v14 v15 v16))))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.ValueRelPER.d_RelD'45'leftself_718
                                               (coe v1) (coe v4) (coe v3) (coe v13)))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5 -> erased
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe
                    (\ v7 v8 ->
                       d_pd'45'D_934
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
                            (coe v5))
                         (coe v2) (coe v3) (coe v4) (coe v7) (coe v8))
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    (\ v7 v8 ->
                       d_ad'45'D_1044
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
                            (coe v5))
                         (coe v2) (coe v3) (coe v4) (coe v7) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_Int_34 -> erased
      MAlonzo.Code.Once.Internal.Type.C_Float_36 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.GradedRelation.GM-D
d_GM'45'D_1246 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_GM'45'D_1246 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'mono_464
      (coe du_'46'extendedlambda0_1364 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146 (coe v1)
         (coe v3))
      (coe v5)
      (coe
         MAlonzo.Code.Once.Denotation.ValueRelPER.du_RelS'45'meet_164
         (coe
            MAlonzo.Code.Once.Internal.Graded.du_toT'8734'_146 (coe v1)
            (coe v3))
         (coe v5) (coe v4) (coe v6) (coe v7))
-- Once.Adequacy.GradedRelation..extendedlambda0
d_'46'extendedlambda0_1364 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_'46'extendedlambda0_1364 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_'46'extendedlambda0_1364 v0 v2 v8 v9 v10
du_'46'extendedlambda0_1364 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_'46'extendedlambda0_1364 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe d_GV'45'D_1234 v0 v1 v2 v5 v3 v7 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
