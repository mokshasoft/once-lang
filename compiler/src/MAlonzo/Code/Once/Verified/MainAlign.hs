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

module MAlonzo.Code.Once.Verified.MainAlign where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.TypeAlias
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Verified.MainAlign.inj₁≢inj₂
d_inj'8321''8802'inj'8322'_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_inj'8321''8802'inj'8322'_16 = erased
-- Once.Verified.MainAlign.inj₂-inj
d_inj'8322''45'inj_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8322''45'inj_28 = erased
-- Once.Verified.MainAlign.MainCf
d_MainCf_30 :: MAlonzo.Code.Once.Compile.T_CompiledFun_186 -> ()
d_MainCf_30 = erased
-- Once.Verified.MainAlign.MainFi
d_MainFi_34 :: MAlonzo.Code.Once.Parser.T_FunInfo_112 -> ()
d_MainFi_34 = erased
-- Once.Verified.MainAlign.compileAllFuns-go-main
d_compileAllFuns'45'go'45'main_50 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_compileAllFuns'45'go'45'main_50 v0 v1 v2 v3 v4 ~v5 ~v6 v7
  = du_compileAllFuns'45'go'45'main_50 v0 v1 v2 v3 v4 v7
du_compileAllFuns'45'go'45'main_50 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_compileAllFuns'45'go'45'main_50 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      (:) v6 v7
        -> let v8
                 = MAlonzo.Code.Once.Compile.d_resolveFunType_260
                     (coe v4) (coe v2)
                     (coe MAlonzo.Code.Once.Parser.d_funType_126 (coe v6))
                     (coe MAlonzo.Code.Once.Parser.d_funBody_130 (coe v6)) in
           coe
             (case coe v8 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                  -> let v10 = MAlonzo.Code.Once.Parser.d_funName_124 (coe v6) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v11 ->
                                        coe
                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                          (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v6)))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                        (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Parser.d_funName_124 (coe v6)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           ("main" :: Data.Text.Text)))) in
                        coe
                          (let v12 = MAlonzo.Code.Once.Parser.d_funBody_130 (coe v6) in
                           coe
                             (if coe v11
                                then let v13
                                           = MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v9) in
                                     coe
                                       (case coe v13 of
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                            -> case coe v13 of
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                                   -> coe
                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                                   -> let v16
                                                            = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_276
                                                                (coe v0) (coe v1) (coe v2) (coe v7)
                                                                (coe
                                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_30
                                                                   (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Parser.d_funName_124
                                                                      (coe v6))
                                                                   (coe v9)) in
                                                      coe
                                                        (case coe v16 of
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                                                             -> coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                                             -> case coe v5 of
                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v20
                                                                    -> coe
                                                                         MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                         v20
                                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v20
                                                                    -> coe
                                                                         MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                                         (coe
                                                                            du_compileAllFuns'45'go'45'main_50
                                                                            (coe v0) (coe v1)
                                                                            (coe v2) (coe v7)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Compile.d_extendFunCtx_30
                                                                               (coe v4)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Parser.d_funName_124
                                                                                  (coe v6))
                                                                               (coe v9))
                                                                            (coe v20))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                            -> let v15
                                                     = MAlonzo.Code.Once.Compile.d_compileFunBody_42
                                                         (coe v0) (coe v1) (coe v4) (coe v2)
                                                         (coe v10) (coe v9) (coe v12) in
                                               coe
                                                 (case coe v15 of
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                                                      -> coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                                                      -> let v17
                                                               = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_276
                                                                   (coe v0) (coe v1) (coe v2)
                                                                   (coe v7)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Compile.d_extendFunCtx_30
                                                                      (coe v4)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Parser.d_funName_124
                                                                         (coe v6))
                                                                      (coe v9)) in
                                                         coe
                                                           (case coe v17 of
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                                                -> coe
                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                                                -> case coe v5 of
                                                                     MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v21
                                                                       -> coe
                                                                            MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                            v21
                                                                     MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v21
                                                                       -> coe
                                                                            MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                                            (coe
                                                                               du_compileAllFuns'45'go'45'main_50
                                                                               (coe v0) (coe v1)
                                                                               (coe v2) (coe v7)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_30
                                                                                  (coe v4)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Parser.d_funName_124
                                                                                     (coe v6))
                                                                                  (coe v9))
                                                                               (coe v21))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                else (let v13
                                            = MAlonzo.Code.Once.Compile.d_compileFunBody_42
                                                (coe v0) (coe v1) (coe v4) (coe v2) (coe v10)
                                                (coe v9) (coe v12) in
                                      coe
                                        (case coe v13 of
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_276
                                                          (coe v0) (coe v1) (coe v2) (coe v7)
                                                          (coe
                                                             MAlonzo.Code.Once.Compile.d_extendFunCtx_30
                                                             (coe v4)
                                                             (coe
                                                                MAlonzo.Code.Once.Parser.d_funName_124
                                                                (coe v6))
                                                             (coe v9)) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                                                       -> coe
                                                            MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                                                       -> case coe v5 of
                                                            MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v19
                                                              -> coe
                                                                   MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                   v19
                                                            MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v19
                                                              -> coe
                                                                   MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                                   (coe
                                                                      du_compileAllFuns'45'go'45'main_50
                                                                      (coe v0) (coe v1) (coe v2)
                                                                      (coe v7)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Compile.d_extendFunCtx_30
                                                                         (coe v4)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Parser.d_funName_124
                                                                            (coe v6))
                                                                         (coe v9))
                                                                      (coe v19))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError)))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.MainAlign.DFunDefMain
d_DFunDefMain_274 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 -> ()
d_DFunDefMain_274 = erased
-- Once.Verified.MainAlign.extractFunctions-go-main
d_extractFunctions'45'go'45'main_292 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_136] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_extractFunctions'45'go'45'main_292 v0 v1 v2 ~v3 ~v4 ~v5 v6
  = du_extractFunctions'45'go'45'main_292 v0 v1 v2 v6
du_extractFunctions'45'go'45'main_292 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_extractFunctions'45'go'45'main_292 v0 v1 v2 v3
  = case coe v1 of
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v6 v7
               -> let v8 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v7) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                         -> coe
                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                              (coe
                                 du_extractFunctions'45'go'45'main_292 (coe v0) (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe
                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                          (coe
                                             MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                             (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.Type.d_extractGround_316 (coe v7)
                                                (coe v9))))))
                                 (coe v3))
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                         -> coe
                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                              (coe
                                 du_extractFunctions'45'go'45'main_292 (coe v0) (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v7))))
                                 (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v6 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                    -> let v13
                                             = coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                 erased
                                                 (\ v13 ->
                                                    coe
                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                      (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                    (coe v10) (coe v6)) in
                                       coe
                                         (case coe v13 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                              -> if coe v14
                                                   then coe
                                                          seq (coe v15)
                                                          (let v16
                                                                 = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                                                                     (coe v0) (coe v5)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                                                           coe
                                                             (case coe v16 of
                                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                                                                  -> coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                                                  -> coe
                                                                       seq (coe v17)
                                                                       (case coe v3 of
                                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v20
                                                                            -> coe
                                                                                 seq (coe v20)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v7)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v8)
                                                                                          erased)))
                                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v20
                                                                            -> coe
                                                                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                                                 (coe
                                                                                    du_extractFunctions'45'go'45'main_292
                                                                                    (coe v0)
                                                                                    (coe v5)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                    (coe v20))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   else coe
                                                          seq (coe v15)
                                                          (coe
                                                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                             (coe
                                                                du_extractFunctions'45'go'45'main_292
                                                                (coe v0) (coe v5)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                (coe v3)))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                    -> let v13
                                             = coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                 erased
                                                 (\ v13 ->
                                                    coe
                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                      (coe v10))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                    (coe v10) (coe v6)) in
                                       coe
                                         (case coe v13 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                              -> if coe v14
                                                   then coe
                                                          seq (coe v15)
                                                          (let v16
                                                                 = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                                                                     (coe v0) (coe v5)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                                                           coe
                                                             (case coe v16 of
                                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                                                                  -> coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                                                  -> coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                                          (coe
                                                                             du_extractFunctions'45'go'45'main_292
                                                                             (coe v0) (coe v5)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                             (coe v3)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   else coe
                                                          seq (coe v15)
                                                          (coe
                                                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                             (coe
                                                                du_extractFunctions'45'go'45'main_292
                                                                (coe v0) (coe v5)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                (coe v3)))
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> let v9
                               = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                                   (coe v0) (coe v5) (coe v2) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                -> coe
                                     seq (coe v10)
                                     (case coe v3 of
                                        MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v13
                                          -> coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v7)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v8) erased)))
                                        MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v13
                                          -> coe
                                               MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                               (coe
                                                  du_extractFunctions'45'go'45'main_292 (coe v0)
                                                  (coe v5) (coe v2) (coe v13))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v6 v7 v8
               -> coe
                    seq (coe v7)
                    (let v9 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v8) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                            -> let v11
                                     = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                                         (coe v0) (coe v5)
                                         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                      -> coe
                                           seq (coe v12)
                                           (case coe v3 of
                                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v15
                                                -> coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                     (coe
                                                        du_extractFunctions'45'go'45'main_292
                                                        (coe v0) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                        (coe v15))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                            -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                          _ -> MAlonzo.RTE.mazUnreachableError))
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v6 v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe
                       du_extractFunctions'45'go'45'main_292 (coe v0) (coe v5) (coe v2)
                       (coe v3))
             MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v6
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe
                       du_extractFunctions'45'go'45'main_292 (coe v0) (coe v5) (coe v2)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.MainAlign.compileResolvedModule-main
d_compileResolvedModule'45'main_1192 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_186] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_compileResolvedModule'45'main_1192 v0 v1 v2 ~v3 ~v4 v5
  = du_compileResolvedModule'45'main_1192 v0 v1 v2 v5
du_compileResolvedModule'45'main_1192 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  Bool ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_compileResolvedModule'45'main_1192 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
              (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v0))
              (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> coe
                       du_extractFunctions'45'go'45'main_292
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v0))
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       (coe
                          du_compileAllFuns'45'go'45'main_50 (coe v1) (coe v2)
                          (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_226 (coe v7))
                          (coe v6) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_28) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
