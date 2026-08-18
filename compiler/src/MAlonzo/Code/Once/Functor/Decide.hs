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

module MAlonzo.Code.Once.Functor.Decide where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.Functor.Decide.isBaseType?
d_isBaseType'63'_8 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200
d_isBaseType'63'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
      MAlonzo.Code.Once.Type.C_Void_124
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204)
      MAlonzo.Code.Once.Type.C__'42'__126 v1 v2
        -> let v3 = d_isBaseType'63'_8 (coe v1) in
           coe
             (let v4 = d_isBaseType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'43'__128 v1 v2
        -> let v3 = d_isBaseType'63'_8 (coe v1) in
           coe
             (let v4 = d_isBaseType'63'_8 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Type.C_Int_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)
      MAlonzo.Code.Once.Type.C_Float_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208)
      MAlonzo.Code.Once.Type.C_Str_140
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210)
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.isConcrete?
d_isConcrete'63'_52 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226
d_isConcrete'63'_52 v0
  = let v1
          = let v1 = d_isBaseType'63'_8 (coe v0) in
            coe
              (case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                   -> coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v2)
                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
           -> let v5 = d_isBaseType'63'_8 (coe v2) in
              coe
                (let v6 = d_isConcrete'63'_52 (coe v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v7 v8)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         _ -> coe v1)
-- Once.Functor.Decide.isBaseType?-complete
d_isBaseType'63''45'complete_90 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isBaseType'63''45'complete_90 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__126 v6 v7
               -> let v8 = d_isBaseType'63''45'complete_90 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_isBaseType'63''45'complete_90 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218
                                           v10 v12)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v6 v7
               -> let v8 = d_isBaseType'63''45'complete_90 (coe v6) (coe v4) in
                  coe
                    (let v9 = d_isBaseType'63''45'complete_90 (coe v7) (coe v5) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v10
                                           v12)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.isConcrete?-complete
d_isConcrete'63''45'complete_152 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isConcrete'63''45'complete_152 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3
        -> case coe v3 of
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3)
                    erased
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3)
                    erased
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3)
                    erased
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3)
                    erased
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3)
                    erased
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v3)
                    erased
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v6 v7
               -> case coe v0 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v8 v9
                      -> let v10
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe d_isBaseType'63''45'complete_90 (coe v8) (coe v6)) in
                         coe
                           (let v11
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe d_isBaseType'63''45'complete_90 (coe v9) (coe v7)) in
                            coe
                              (let v12
                                     = coe
                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v10
                                         v11 in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v12)
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v6 v7
               -> case coe v0 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
                      -> let v10
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe d_isBaseType'63''45'complete_90 (coe v8) (coe v6)) in
                         coe
                           (let v11
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe d_isBaseType'63''45'complete_90 (coe v9) (coe v7)) in
                            coe
                              (let v12
                                     = coe
                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v10
                                         v11 in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v12)
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v7 v8 v9
               -> let v10 = d_isBaseType'63''45'complete_90 (coe v7) (coe v5) in
                  coe
                    (let v11 = d_isConcrete'63''45'complete_152 (coe v9) (coe v6) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v12
                                           v14)
                                        erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Decide.wellFormedF?
d_wellFormedF'63'_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
d_wellFormedF'63'_224 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v1
        -> let v2 = d_isBaseType'63'_8 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v3)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246)
      MAlonzo.Code.Once.Type.C__'8853'__118 v1 v2
        -> let v3 = d_wellFormedF'63'_224 (coe v1) in
           coe
             (let v4 = d_wellFormedF'63'_224 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Type.C__'8855'__120 v1 v2
        -> let v3 = d_wellFormedF'63'_224 (coe v1) in
           coe
             (let v4 = d_wellFormedF'63'_224 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v5 v6)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
