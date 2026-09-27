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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Admissible
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98 ->
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'aux'45'doOpt_28 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                (coe
                   MAlonzo.Code.Once.Optimize.d_optimize_2418
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe v1)))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v6))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_984 (coe v0)
                      (coe v1) (coe v8) (coe v6)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3916
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
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_984 (coe v0)
                   (coe v1) (coe v8) (coe v6)
                   (coe
                      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3916
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
d_cfb'45'doOpt_76 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'doOpt_76 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_cfb'45'doOpt_76 v0 v1 v2 v3 v4 v5
du_cfb'45'doOpt_76 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'doOpt_76 v0 v1 v2 v3 v4 v5
  = coe
      du_cfb'45'aux'45'doOpt_28 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1360
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
            (coe v1) (coe v2) (coe v3) (coe v4))
         (coe v5) (coe v4))
-- Once.Adequacy.MainBuilds.cfun-main-aux-doOpt
d_cfun'45'main'45'aux'45'doOpt_110 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'main'45'aux'45'doOpt_110 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfun'45'main'45'aux'45'doOpt_110 v0 v1 v2 v3 v4 v5 v6
du_cfun'45'main'45'aux'45'doOpt_110 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'main'45'aux'45'doOpt_110 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v6)
      (coe
         du_cfb'45'doOpt_76 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
-- Once.Adequacy.MainBuilds.cfun-aux-doOpt
d_cfun'45'aux'45'doOpt_158 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'aux'45'doOpt_158 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfun'45'aux'45'doOpt_158 v0 v1 v2 v3 v4 v5 v6
du_cfun'45'aux'45'doOpt_158 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'aux'45'doOpt_158 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             du_cfun'45'main'45'aux'45'doOpt_110 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v4))
      else coe
             du_cfb'45'doOpt_76 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
-- Once.Adequacy.MainBuilds.cfun-doOpt
d_cfun'45'doOpt_204 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'doOpt_204 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_cfun'45'doOpt_204 v0 v1 v2 v3 v4 v5
du_cfun'45'doOpt_204 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'doOpt_204 v0 v1 v2 v3 v4 v5
  = coe
      du_cfun'45'aux'45'doOpt_158 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v3)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.MainBuilds.caf-go-doOpt
d_caf'45'go'45'doOpt_232 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'doOpt_232 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'go'45'doOpt_232 v0 v1 v2 v3
du_caf'45'go'45'doOpt_232 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'doOpt_232 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      (:) v4 v5
        -> coe
             du_caf'45'go'45'rf'45'doOpt_268 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_344 (coe v3) (coe v1)
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v4))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.caf-go-cf-doOpt
d_caf'45'go'45'cf'45'doOpt_250 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'cf'45'doOpt_250 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_caf'45'go'45'cf'45'doOpt_250 v0 v1 v2 v3 v4 v5
du_caf'45'go'45'cf'45'doOpt_250 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'cf'45'doOpt_250 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Compile.du_compileFun'45'aux_184
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4) (coe v1)
              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)
              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> let v8
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_376
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                                (coe
                                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            du_cfun'45'doOpt_204 (coe v0) (coe v4) (coe v1)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            du_cfun'45'doOpt_204 (coe v0) (coe v4) (coe v1)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))))
                                (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v2)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   du_caf'45'go'45'doOpt_232 (coe v0) (coe v1) (coe v3)
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4)
                                      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                      (coe v5)))))
                          erased
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.MainBuilds.caf-go-rf-doOpt
d_caf'45'go'45'rf'45'doOpt_268 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'rf'45'doOpt_268 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_caf'45'go'45'rf'45'doOpt_268 v0 v1 v2 v3 v4 v5
du_caf'45'go'45'rf'45'doOpt_268 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'rf'45'doOpt_268 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_caf'45'go'45'cf'45'doOpt_250 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.caf-doOpt
d_caf'45'doOpt_428 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'doOpt_428 v0 v1 v2 ~v3 ~v4 = du_caf'45'doOpt_428 v0 v1 v2
du_caf'45'doOpt_428 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'doOpt_428 v0 v1 v2
  = coe
      du_caf'45'go'45'doOpt_232 (coe v0) (coe v2) (coe v1)
      (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64)
-- Once.Adequacy.MainBuilds.crm-aux-doOpt
d_crm'45'aux'45'doOpt_448 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'aux'45'doOpt_448 v0 ~v1 v2 ~v3 ~v4
  = du_crm'45'aux'45'doOpt_448 v0 v2
du_crm'45'aux'45'doOpt_448 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'aux'45'doOpt_448 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_caf'45'doOpt_428 (coe v0) (coe v3)
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.crm-doOpt
d_crm'45'doOpt_474 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'doOpt_474 v0 v1 ~v2 ~v3 = du_crm'45'doOpt_474 v0 v1
du_crm'45'doOpt_474 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'doOpt_474 v0 v1
  = coe
      du_crm'45'aux'45'doOpt_448 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_514
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
-- Once.Adequacy.MainBuilds.cfm-built-gated
d_cfm'45'built'45'gated_498 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'gated_498 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8
  = du_cfm'45'built'45'gated_498 v1 v5 v7
du_cfm'45'built'45'gated_498 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'gated_498 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (MAlonzo.Code.Once.Target.d_asmHeader_28
                             (coe MAlonzo.Code.Once.Compile.d_archTarget_582 (coe v0)))
                          (MAlonzo.Code.Once.Compile.d_compileAllWithTarget_618
                             (coe MAlonzo.Code.Once.Compile.d_archTarget_582 (coe v0))
                             (coe v2)))
                       erased)
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfm-built-aux
d_cfm'45'built'45'aux_542 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'aux_542 ~v0 v1 v2 ~v3 v4 v5 ~v6
  = du_cfm'45'built'45'aux_542 v1 v2 v4 v5
du_cfm'45'built'45'aux_542 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'aux_542 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             seq (coe v4)
             (coe
                du_cfm'45'built'45'gated_498 (coe v0)
                (coe
                   MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                   (coe v0) (coe v1))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfm-built-from-crm
d_cfm'45'built'45'from'45'crm_578 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'from'45'crm_578 ~v0 v1 v2 ~v3 v4 ~v5
  = du_cfm'45'built'45'from'45'crm_578 v1 v2 v4
du_cfm'45'built'45'from'45'crm_578 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'from'45'crm_578 v0 v1 v2
  = coe
      du_cfm'45'built'45'aux_542 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_514
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.MainBuilds.mtir-aux-inj₂
d_mtir'45'aux'45'inj'8322'_596 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mtir'45'aux'45'inj'8322'_596 v0 ~v1 ~v2
  = du_mtir'45'aux'45'inj'8322'_596 v0
du_mtir'45'aux'45'inj'8322'_596 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mtir'45'aux'45'inj'8322'_596 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.moduleToIR-inj₂
d_moduleToIR'45'inj'8322'_608 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'inj'8322'_608 v0 ~v1 ~v2
  = du_moduleToIR'45'inj'8322'_608 v0
du_moduleToIR'45'inj'8322'_608 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToIR'45'inj'8322'_608 v0
  = coe
      du_mtir'45'aux'45'inj'8322'_596
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_546
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.MainBuilds.main⇒built
d_main'8658'built_624 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'8658'built_624 v0 v1 v2 ~v3 ~v4 ~v5
  = du_main'8658'built_624 v0 v1 v2
du_main'8658'built_624 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'8658'built_624 v0 v1 v2
  = coe
      du_cfm'45'built'45'from'45'crm_578 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_crm'45'doOpt_474 (coe v1) (coe v2)))
