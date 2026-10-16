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

module MAlonzo.Code.Once.Denotation.GuardedLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Lang.Guarded
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial

-- Once.Denotation.GuardedLaws.forget-bind⁺
d_forget'45'bind'8314'_14 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_forget'45'bind'8314'_14 ~v0 ~v1 v2 v3
  = du_forget'45'bind'8314'_14 v2 v3
du_forget'45'bind'8314'_14 ::
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_forget'45'bind'8314'_14 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64 v2 v3 v4
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'refl_14
                     erased
                     (coe
                        MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                        (coe v4 v5) (coe v1)))
         MAlonzo.Code.Once.Lang.Guarded.C_halt'8314'_68 v2 v3
           -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.GuardedLaws.forget-⁺bind
d_forget'45''8314'bind_44 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_forget'45''8314'bind_44 ~v0 ~v1 v2 v3
  = du_forget'45''8314'bind_44 v2 v3
du_forget'45''8314'bind_44 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_forget'45''8314'bind_44 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_forget'45''8314'bindF_56
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0))
         (coe v1))
-- Once.Denotation.GuardedLaws.forget-⁺bindF
d_forget'45''8314'bindF_56 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_forget'45''8314'bindF_56 ~v0 ~v1 v2 v3
  = du_forget'45''8314'bindF_56 v2 v3
du_forget'45''8314'bindF_56 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_forget'45''8314'bindF_56 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v2
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'reflF_24
             erased
             (coe MAlonzo.Code.Once.Lang.Guarded.du_root'8314'_72 (coe v1 v2))
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
             (\ v5 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'refl_14
                  erased
                  (coe
                     MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                     (coe v4 v5)
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v6)))))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v2 v3
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.GuardedLaws.forget-anaRoot
d_forget'45'anaRoot_94 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_forget'45'anaRoot_94 v0 ~v1 v2 v3
  = du_forget'45'anaRoot_94 v0 v2 v3
du_forget'45'anaRoot_94 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_forget'45'anaRoot_94 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (case coe v2 of
         MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64 v3 v4 v5
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                (\ v6 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'refl_14
                     erased
                     (coe
                        MAlonzo.Code.Once.Lang.Guarded.du_anaTree'8314'_190 (coe v0)
                        (coe v1) (coe v5 v6)))
         MAlonzo.Code.Once.Lang.Guarded.C_halt'8314'_68 v3 v4
           -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.GuardedLaws.assoc⁺
d_assoc'8314'_138 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_assoc'8314'_138 ~v0 ~v1 ~v2 v3 v4 v5
  = du_assoc'8314'_138 v3 v4 v5
du_assoc'8314'_138 ::
  MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Guarded.T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_assoc'8314'_138 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Guarded.C_call'8314'_64 v3 v4 v5
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                (\ v6 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'rewrite_308
                     (coe
                        MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                        (coe
                           MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                           (coe v5 v6)
                           (coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v7))))
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v2 v7))))
                     (coe
                        MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                        (coe v5 v6)
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                                (coe MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v7))
                                (coe
                                   (\ v8 ->
                                      coe
                                        MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                        (coe v2 v8))))))
                     (coe
                        MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                        (coe v5 v6)
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                (coe
                                   MAlonzo.Code.Once.Lang.Guarded.du__'62''62''61''8314'__94
                                   (coe v1 v7)
                                   (coe
                                      (\ v8 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                           (coe v2 v8)))))))
                     (coe
                        MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                        (coe v5 v6)
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                                (coe MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v7))
                                (coe
                                   (\ v8 ->
                                      coe
                                        MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                        (coe v2 v8))))))
                     (coe
                        MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'assoc_446
                        (coe v5 v6)
                        (coe
                           (\ v7 ->
                              coe MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v7)))
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v2 v7))))
                     (coe
                        MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'bind_70
                        (coe v5 v6) (coe v5 v6)
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                (coe
                                   MAlonzo.Code.Once.Lang.Guarded.du__'62''62''61''8314'__94
                                   (coe v1 v7)
                                   (coe
                                      (\ v8 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                           (coe v2 v8))))))
                        (coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                                (coe MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v7))
                                (coe
                                   (\ v8 ->
                                      coe
                                        MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                        (coe v2 v8)))))
                        (coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'refl_14
                           erased (coe v5 v6))
                        (coe
                           (\ v7 v8 v9 ->
                              coe
                                du_forget'45'bind'8314'_14 (coe v1 v7)
                                (coe
                                   (\ v10 ->
                                      coe
                                        MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                        (coe v2 v10))))))
                     (coe
                        MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_'8776''8734''45'refl_14
                        erased
                        (coe
                           MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                           (coe v5 v6)
                           (coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                                   (coe
                                      MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86 (coe v1 v7))
                                   (coe
                                      (\ v8 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Guarded.du_forget'8314'_86
                                           (coe v2 v8))))))))
         MAlonzo.Code.Once.Lang.Guarded.C_halt'8314'_68 v3 v4
           -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
         _ -> MAlonzo.RTE.mazUnreachableError)
