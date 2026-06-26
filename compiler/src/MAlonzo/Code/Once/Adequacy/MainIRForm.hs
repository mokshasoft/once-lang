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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
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
-- Once.Adequacy.MainIRForm.validateMain-EffUU
d_validateMain'45'EffUU_10 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_validateMain'45'EffUU_10 = erased
-- Once.Adequacy.MainIRForm.compileFunBody-form
d_compileFunBody'45'form_80 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'form_80 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_compileFunBody'45'form_80 v0 v1 v2 v3 v4
du_compileFunBody'45'form_80 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'form_80 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1298
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                  (coe v0) (coe v1) (coe v2) (coe v3) (coe d_EffUU_6))
               (coe v4) (coe d_EffUU_6))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolveExpr_12596
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe d_EffUU_6)
            (coe v1)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                  (coe d_EffUU_6))
               (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                  (coe d_EffUU_6))
               (coe v0))
            (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1298
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                           (coe v0) (coe v1) (coe v2) (coe v3) (coe d_EffUU_6))
                        (coe v4) (coe d_EffUU_6))))))
         erased)
-- Once.Adequacy.MainIRForm.compileFun-main-reduces
d_compileFun'45'main'45'reduces_122 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compileFun'45'main'45'reduces_122 = erased
-- Once.Adequacy.MainIRForm.compileFun-main-EffUU
d_compileFun'45'main'45'EffUU_146 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compileFun'45'main'45'EffUU_146 = erased
-- Once.Adequacy.MainIRForm.compileFun-main-formEffUU
d_compileFun'45'main'45'formEffUU_212 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'formEffUU_212 v0 v1 v2 v3 ~v4 ~v5
  = du_compileFun'45'main'45'formEffUU_212 v0 v1 v2 v3
du_compileFun'45'main'45'formEffUU_212 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'formEffUU_212 v0 v1 v2 v3
  = coe
      du_compileFunBody'45'form_80 (coe v0) (coe v1) (coe v2)
      (coe ("main" :: Data.Text.Text)) (coe v3)
-- Once.Adequacy.MainIRForm.compileFun-main-form
d_compileFun'45'main'45'form_244 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'form_244 v0 v1 v2 ~v3 v4 ~v5 ~v6
  = du_compileFun'45'main'45'form_244 v0 v1 v2 v4
du_compileFun'45'main'45'form_244 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'form_244 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         du_compileFun'45'main'45'formEffUU_212 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Once.Adequacy.MainIRForm.findMain-here-no
d_findMain'45'here'45'no_288 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  Bool ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'here'45'no_288 = erased
-- Once.Adequacy.MainIRForm.bare-injective
d_bare'45'injective_310 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bare'45'injective_310 = erased
-- Once.Adequacy.MainIRForm.findMain-skip
d_findMain'45'skip_316 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'skip_316 = erased
-- Once.Adequacy.MainIRForm.Form
d_Form_344 :: MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Form_344 = erased
-- Once.Adequacy.MainIRForm.caf-go-find-form
d_caf'45'go'45'find'45'form_364 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'find'45'form_364 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
  = du_caf'45'go'45'find'45'form_364 v0 v1 v2 v3
du_caf'45'go'45'find'45'form_364 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'find'45'form_364 v0 v1 v2 v3
  = case coe v2 of
      [] -> erased
      (:) v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Compile.d_resolveFunType_304
                     (coe v3) (coe v0)
                     (coe MAlonzo.Code.Once.Parser.d_funType_126 (coe v4))
                     (coe MAlonzo.Code.Once.Parser.d_funBody_130 (coe v4)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                  -> let v8
                           = MAlonzo.Code.Once.Compile.d_compileFun'45'aux_174
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3) (coe v0)
                               (coe v1) (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v4))
                               (coe v7) (coe MAlonzo.Code.Once.Parser.d_funBody_130 (coe v4))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                          (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v4)))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                        (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Parser.d_funName_124 (coe v4)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           ("main" :: Data.Text.Text))))) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                            -> let v10
                                     = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_336
                                         (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0)
                                         (coe v1) (coe v5)
                                         (coe
                                            MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_124 (coe v4))
                                            (coe v7)) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11 -> erased
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                      -> let v12
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v12 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe
                                                           MAlonzo.Code.Once.Parser.d_funName_124
                                                           (coe v4)))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funName_124
                                                         (coe v4))
                                                      (coe ("main" :: Data.Text.Text))) in
                                         coe
                                           (case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                -> if coe v13
                                                     then coe
                                                            seq (coe v14)
                                                            (case coe v4 of
                                                               MAlonzo.Code.Once.Parser.C_mkFunInfo_134 v15 v16 v17 v18 v19
                                                                 -> if coe v19
                                                                      then coe
                                                                             du_caf'45'go'45'find'45'form_364
                                                                             (coe v0) (coe v1)
                                                                             (coe v5)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                                                (coe v3)
                                                                                (coe
                                                                                   ("main"
                                                                                    ::
                                                                                    Data.Text.Text))
                                                                                (coe v7))
                                                                      else (let v20
                                                                                  = coe
                                                                                      du_compileFun'45'main'45'formEffUU_212
                                                                                      (coe v3)
                                                                                      (coe v0)
                                                                                      (coe v1)
                                                                                      (coe v18) in
                                                                            coe
                                                                              (case coe v20 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                   -> case coe
                                                                                             v22 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v21)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     v23)
                                                                                                  erased)
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     else coe
                                                            seq (coe v14)
                                                            (coe
                                                               du_caf'45'go'45'find'45'form_364
                                                               (coe v0) (coe v1) (coe v5)
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                                  (coe v3)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Parser.d_funName_124
                                                                     (coe v4))
                                                                  (coe v7)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainIRForm.main-ir-form
d_main'45'ir'45'form_702 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'ir'45'form_702 v0 ~v1 ~v2 = du_main'45'ir'45'form_702 v0
du_main'45'ir'45'form_702 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'ir'45'form_702 v0
  = let v1
          = MAlonzo.Code.Once.Parser.d_guardDistinct_492
              (coe
                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_206
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_92 (coe v0))
                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> let v5
                           = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_336
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Compile.d_collectSigEffects_462
                                  (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                               (coe v3) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> erased
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                            -> coe
                                 du_caf'45'go'45'find'45'form_364
                                 (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v4))
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_collectSigEffects_462
                                    (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                                 (coe v3) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
