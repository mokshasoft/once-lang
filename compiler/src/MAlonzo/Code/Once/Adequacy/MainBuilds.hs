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

module MAlonzo.Code.Once.Adequacy.MainBuilds where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.MainBuilds.cfb-aux-doOpt
d_cfb'45'aux'45'doOpt_28 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_326 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'aux'45'doOpt_28 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_cfb'45'aux'45'doOpt_28 v0 v1 v2 v3 v4 v5 v6 v8
du_cfb'45'aux'45'doOpt_28 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_326 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'aux'45'doOpt_28 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                (coe
                   MAlonzo.Code.Once.Optimize.d_optimize_4296
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe v1)))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_246 (coe v1)
                      (coe v6) (coe MAlonzo.Code.Once.IR.C_Heap_8)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_2878
                         (coe v0) (coe v1) (coe v6) (coe v4)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
                            (coe v3))
                         (coe (0 :: Integer)) (coe v9))))
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_246 (coe v1)
                   (coe v6) (coe MAlonzo.Code.Once.IR.C_Heap_8)
                   (coe
                      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_2878
                      (coe v0) (coe v1) (coe v6) (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
                         (coe v3))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
                         (coe v3))
                      (coe (0 :: Integer)) (coe v9))))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfb-doOpt
d_cfb'45'doOpt_78 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'doOpt_78 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfb'45'doOpt_78 v0 v1 v2 v3 v4 v5 v6
du_cfb'45'doOpt_78 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'doOpt_78 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cfb'45'aux'45'doOpt_28 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v0)
      (coe v1) (coe v2) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1676
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
            (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
         (coe v6) (coe v5))
-- Once.Adequacy.MainBuilds.cfun-main-aux-doOpt
d_cfun'45'main'45'aux'45'doOpt_116 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'main'45'aux'45'doOpt_116 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_cfun'45'main'45'aux'45'doOpt_116 v0 v1 v2 v3 v4 v5 v6 v7
du_cfun'45'main'45'aux'45'doOpt_116 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'main'45'aux'45'doOpt_116 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (coe
         du_cfb'45'doOpt_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6))
-- Once.Adequacy.MainBuilds.cfun-aux-doOpt
d_cfun'45'aux'45'doOpt_170 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'aux'45'doOpt_170 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_cfun'45'aux'45'doOpt_170 v0 v1 v2 v3 v4 v5 v6 v7
du_cfun'45'aux'45'doOpt_170 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'aux'45'doOpt_170 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_cfun'45'main'45'aux'45'doOpt_116 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v5))
      else coe
             du_cfb'45'doOpt_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Adequacy.MainBuilds.cfun-doOpt
d_cfun'45'doOpt_222 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'doOpt_222 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfun'45'doOpt_222 v0 v1 v2 v3 v4 v5 v6
du_cfun'45'doOpt_222 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'doOpt_222 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cfun'45'aux'45'doOpt_170 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.MainBuilds.caf-go-doOpt
d_caf'45'go'45'doOpt_254 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'doOpt_254 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_caf'45'go'45'doOpt_254 v0 v1 v2 v3 v4
du_caf'45'go'45'doOpt_254 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'doOpt_254 v0 v1 v2 v3 v4
  = case coe v3 of
      []
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased
      (:) v5 v6
        -> coe
             du_caf'45'go'45'rf'45'doOpt_294 (coe v0) (coe v1) (coe v2) (coe v5)
             (coe v6) (coe v4)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_340 (coe v4) (coe v1)
                (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v5))
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.caf-go-cf-doOpt
d_caf'45'go'45'cf'45'doOpt_274 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'cf'45'doOpt_274 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_caf'45'go'45'cf'45'doOpt_274 v0 v1 v2 v3 v4 v5 v6
du_caf'45'go'45'cf'45'doOpt_274 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'cf'45'doOpt_274 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Compile.d_compileFun'45'aux_174
              (coe MAlonzo.Code.Once.IR.C_Heap_8)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v5) (coe v1)
              (coe v2) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
              (coe v6) (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v7 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> let v9
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) (coe v2)
                        (coe v4)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                           (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
                                (coe
                                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                                   (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            du_cfun'45'doOpt_222 (coe v0) (coe v5) (coe v1) (coe v2)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
                                            (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            du_cfun'45'doOpt_222 (coe v0) (coe v5) (coe v1) (coe v2)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
                                            (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))))))
                                (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v3)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   du_caf'45'go'45'doOpt_254 (coe v0) (coe v1) (coe v2) (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                                      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
                                      (coe v6)))))
                          erased
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.MainBuilds.caf-go-rf-doOpt
d_caf'45'go'45'rf'45'doOpt_294 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'rf'45'doOpt_294 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_caf'45'go'45'rf'45'doOpt_294 v0 v1 v2 v3 v4 v5 v6
du_caf'45'go'45'rf'45'doOpt_294 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'rf'45'doOpt_294 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             du_caf'45'go'45'cf'45'doOpt_274 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.caf-doOpt
d_caf'45'doOpt_474 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'doOpt_474 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'doOpt_474 v0 v1 v2 v3
du_caf'45'doOpt_474 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'doOpt_474 v0 v1 v2 v3
  = coe
      du_caf'45'go'45'doOpt_254 (coe v0) (coe v2) (coe v3) (coe v1)
      (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)
-- Once.Adequacy.MainBuilds.crm-aux-doOpt
d_crm'45'aux'45'doOpt_496 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'aux'45'doOpt_496 v0 v1 v2 ~v3 ~v4
  = du_crm'45'aux'45'doOpt_496 v0 v1 v2
du_crm'45'aux'45'doOpt_496 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'aux'45'doOpt_496 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_caf'45'doOpt_474 (coe v0) (coe v4)
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v5))
                    (coe
                       MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.crm-doOpt
d_crm'45'doOpt_522 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'doOpt_522 v0 v1 ~v2 ~v3 = du_crm'45'doOpt_522 v0 v1
du_crm'45'doOpt_522 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'doOpt_522 v0 v1
  = coe
      du_crm'45'aux'45'doOpt_496 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
-- Once.Adequacy.MainBuilds.cfm-built-aux
d_cfm'45'built'45'aux_542 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'aux_542 ~v0 v1 ~v2 v3 v4 ~v5
  = du_cfm'45'built'45'aux_542 v1 v3 v4
du_cfm'45'built'45'aux_542 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'aux_542 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Target.d_asmHeader_40
                      (coe MAlonzo.Code.Once.Compile.d_archTarget_642 (coe v0)))
                   (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_682
                      (coe MAlonzo.Code.Once.Compile.d_archTarget_642 (coe v0))
                      (coe v2)))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfm-built-from-crm
d_cfm'45'built'45'from'45'crm_574 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'from'45'crm_574 ~v0 v1 v2 v3 ~v4
  = du_cfm'45'built'45'from'45'crm_574 v1 v2 v3
du_cfm'45'built'45'from'45'crm_574 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'from'45'crm_574 v0 v1 v2
  = coe
      du_cfm'45'built'45'aux_542 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.MainBuilds.mtir-aux-inj₂
d_mtir'45'aux'45'inj'8322'_590 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mtir'45'aux'45'inj'8322'_590 v0 ~v1 ~v2
  = du_mtir'45'aux'45'inj'8322'_590 v0
du_mtir'45'aux'45'inj'8322'_590 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mtir'45'aux'45'inj'8322'_590 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.moduleToIR-inj₂
d_moduleToIR'45'inj'8322'_602 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'inj'8322'_602 v0 ~v1 ~v2
  = du_moduleToIR'45'inj'8322'_602 v0
du_moduleToIR'45'inj'8322'_602 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToIR'45'inj'8322'_602 v0
  = coe
      du_mtir'45'aux'45'inj'8322'_590
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_574
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.MainBuilds.main⇒built
d_main'8658'built_618 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'8658'built_618 v0 v1 v2 ~v3 ~v4
  = du_main'8658'built_618 v0 v1 v2
du_main'8658'built_618 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'8658'built_618 v0 v1 v2
  = coe
      du_cfm'45'built'45'from'45'crm_574 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_crm'45'doOpt_522 (coe v1) (coe v2)))
