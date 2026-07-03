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

module MAlonzo.Code.Once.Adequacy.MainIRForm where

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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.MainIRForm.EffUU
d_EffUU_6 :: MAlonzo.Code.Once.Type.T_Type_112
d_EffUU_6
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
-- Once.Adequacy.MainIRForm.Payload
d_Payload_10 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 -> ()
d_Payload_10 = erased
-- Once.Adequacy.MainIRForm.BodyForm
d_BodyForm_32 :: MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_BodyForm_32 = erased
-- Once.Adequacy.MainIRForm.validateMain-EffUU
d_validateMain'45'EffUU_42 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_validateMain'45'EffUU_42 = erased
-- Once.Adequacy.MainIRForm.compileFunBody-form
d_compileFunBody'45'form_106 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'form_106 v0 v1 v2 v3 ~v4 ~v5
  = du_compileFunBody'45'form_106 v0 v1 v2 v3
du_compileFunBody'45'form_106 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'form_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1506
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                  (coe v0) (coe v1) (coe v2) (coe ("main" :: Data.Text.Text))
                  (coe d_EffUU_6))
               (coe v3) (coe d_EffUU_6))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_12206
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe d_EffUU_6)
            (coe v1)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe ("main" :: Data.Text.Text)) (coe d_EffUU_6))
               (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe ("main" :: Data.Text.Text)) (coe d_EffUU_6))
               (coe v0))
            (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1506
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                           (coe v0) (coe v1) (coe v2) (coe ("main" :: Data.Text.Text))
                           (coe d_EffUU_6))
                        (coe v3) (coe d_EffUU_6))))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1506
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                                          (coe v0) (coe v1) (coe v2)
                                          (coe ("main" :: Data.Text.Text)) (coe d_EffUU_6))
                                       (coe v3) (coe d_EffUU_6)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1506
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                                                (coe v0) (coe v1) (coe v2)
                                                (coe ("main" :: Data.Text.Text)) (coe d_EffUU_6))
                                             (coe v3) (coe d_EffUU_6))))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1506
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                                                      (coe v0) (coe v1) (coe v2)
                                                      (coe ("main" :: Data.Text.Text))
                                                      (coe d_EffUU_6))
                                                   (coe v3) (coe d_EffUU_6)))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1506
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                                                         (coe v0) (coe v1) (coe v2)
                                                         (coe ("main" :: Data.Text.Text))
                                                         (coe d_EffUU_6))
                                                      (coe v3) (coe d_EffUU_6)))))))
                                    erased))))))))))
-- Once.Adequacy.MainIRForm.compileFun-main-reduces
d_compileFun'45'main'45'reduces_146 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compileFun'45'main'45'reduces_146 = erased
-- Once.Adequacy.MainIRForm.compileFun-main-EffUU
d_compileFun'45'main'45'EffUU_170 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compileFun'45'main'45'EffUU_170 = erased
-- Once.Adequacy.MainIRForm.compileFun-main-formEffUU
d_compileFun'45'main'45'formEffUU_232 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'formEffUU_232 v0 v1 v2 v3 ~v4 ~v5
  = du_compileFun'45'main'45'formEffUU_232 v0 v1 v2 v3
du_compileFun'45'main'45'formEffUU_232 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'formEffUU_232 v0 v1 v2 v3
  = coe
      du_compileFunBody'45'form_106 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.MainIRForm.compileFun-main-form
d_compileFun'45'main'45'form_260 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'form_260 v0 v1 v2 ~v3 v4 ~v5 ~v6
  = du_compileFun'45'main'45'form_260 v0 v1 v2 v4
du_compileFun'45'main'45'form_260 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'form_260 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         du_compileFun'45'main'45'formEffUU_232 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Once.Adequacy.MainIRForm.findMain-here-no
d_findMain'45'here'45'no_304 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  Bool ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'here'45'no_304 = erased
-- Once.Adequacy.MainIRForm.bare-injective
d_bare'45'injective_326 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bare'45'injective_326 = erased
-- Once.Adequacy.MainIRForm.findMain-skip
d_findMain'45'skip_332 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'skip_332 = erased
-- Once.Adequacy.MainIRForm.findMain-skip-prim
d_findMain'45'skip'45'prim_364 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'skip'45'prim_364 = erased
-- Once.Adequacy.MainIRForm.Form
d_Form_376 :: MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Form_376 = erased
-- Once.Adequacy.MainIRForm.caf-go-find-form
d_caf'45'go'45'find'45'form_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'find'45'form_396 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7
  = du_caf'45'go'45'find'45'form_396 v0 v1 v2 v3 v5
du_caf'45'go'45'find'45'form_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'find'45'form_396 v0 v1 v2 v3 v4
  = case coe v2 of
      [] -> erased
      (:) v5 v6
        -> coe
             du_cff'45'rf_414 (coe v0) (coe v1) (coe v5) (coe v6) (coe v3)
             (coe v4)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_304 (coe v3) (coe v0)
                (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v5))
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.cff-rf
d_cff'45'rf_414 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cff'45'rf_414 v0 v1 v2 v3 v4 ~v5 v6 v7 ~v8 ~v9
  = du_cff'45'rf_414 v0 v1 v2 v3 v4 v6 v7
du_cff'45'rf_414 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cff'45'rf_414 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             du_cff'45'cf_434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v7) (coe v5)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFun_212
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4) (coe v0)
                (coe v1) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2))
                (coe v7) (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.cff-cf
d_cff'45'cf_434 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cff'45'cf_434 v0 v1 v2 v3 v4 v5 ~v6 v7 v8 ~v9 ~v10 ~v11
  = du_cff'45'cf_434 v0 v1 v2 v3 v4 v5 v7 v8
du_cff'45'cf_434 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cff'45'cf_434 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (coe
         du_cff'45'rec_458 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6)
         (coe
            MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_336
            (coe MAlonzo.Code.Once.IR.C_Heap_8)
            (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v1)
            (coe v3)
            (coe
               MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v4)
               (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2)) (coe v5))))
-- Once.Adequacy.MainIRForm.cff-rec
d_cff'45'rec_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cff'45'rec_458 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9 v10 ~v11 ~v12
                 ~v13
  = du_cff'45'rec_458 v0 v1 v2 v3 v4 v5 v8 v10
du_cff'45'rec_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cff'45'rec_458 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             du_cff'45'dispatch_490 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2))
             (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v2)) (coe v3)
             (coe v4) (coe v5) (coe v8) (coe v6)
             (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v2))
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2))
                (coe ("main" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.cff-dispatch
d_cff'45'dispatch_490 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cff'45'dispatch_490 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 v9 v10 ~v11 ~v12
                      ~v13 v14
  = du_cff'45'dispatch_490 v0 v1 v2 v3 v4 v5 v6 v8 v9 v10 v14
du_cff'45'dispatch_490 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cff'45'dispatch_490 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then if coe v9
                    then coe
                           seq (coe v12)
                           (coe
                              du_caf'45'go'45'find'45'form_396 (coe v0) (coe v1) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                                 (coe ("main" :: Data.Text.Text)) (coe v6))
                              (coe v8))
                    else coe
                           seq (coe v12)
                           (coe
                              du_cff'45'stop_514
                              (coe
                                 du_compileFun'45'main'45'form_260 (coe v5) (coe v0) (coe v1)
                                 (coe v3)))
             else coe
                    seq (coe v12)
                    (coe
                       du_caf'45'go'45'find'45'form_396 (coe v0) (coe v1) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5) (coe v2)
                          (coe v6))
                       (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.cff-stop
d_cff'45'stop_514 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cff'45'stop_514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_cff'45'stop_514 v8
du_cff'45'stop_514 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cff'45'stop_514 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.main-ir-form
d_main'45'ir'45'form_804 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'ir'45'form_804 v0 v1 ~v2
  = du_main'45'ir'45'form_804 v0 v1
du_main'45'ir'45'form_804 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'ir'45'form_804 v0 v1
  = coe
      du_mif'45'ef_852 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_490
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
         (coe v0))
-- Once.Adequacy.MainIRForm.mif-caf
d_mif'45'caf_816 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mif'45'caf_816 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_mif'45'caf_816 v0 v1 v2 v3 v4
du_mif'45'caf_816 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mif'45'caf_816 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             du_caf'45'go'45'find'45'form_396
             (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v3))
             (coe
                MAlonzo.Code.Once.Compile.d_collectSigEffects_462
                (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
             (coe v2) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.mif-ef
d_mif'45'ef_852 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mif'45'ef_852 v0 v1 v2 ~v3 = du_mif'45'ef_852 v0 v1 v2
du_mif'45'ef_852 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mif'45'ef_852 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_mif'45'caf_816 (coe v0) (coe v1) (coe v4) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_336
                       (coe MAlonzo.Code.Once.IR.C_Heap_8)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v5))
                       (coe
                          MAlonzo.Code.Once.Compile.d_collectSigEffects_462
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                       (coe v4) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
