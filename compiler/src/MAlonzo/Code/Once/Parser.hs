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

module MAlonzo.Code.Once.Parser where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeAlias
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Principal
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.parse
d_parse_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_parse_4 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Parser.Module.d_r_370
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_1038 (coe v0)))) in
    coe (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
-- Once.Parser.allTrailing
d_allTrailing_18 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_allTrailing_18 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TNewline_74
                  -> coe d_allTrailing_18 (coe v3)
                MAlonzo.Code.Once.Parser.Token.C_TEOF_76
                  -> coe d_allTrailing_18 (coe v3)
                _ -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.showTokenPrefix
d_showTokenPrefix_24 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTokenPrefix_24 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.Token.C_TWord_8 v3
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("TWord \"" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                       ("\"" :: Data.Text.Text))
             MAlonzo.Code.Once.Parser.Token.C_TInt_10 v3 v4
               -> coe ("TInt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v3 v4 v5 v6
               -> coe ("TFloat" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TString_14 v3
               -> coe ("TString" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLParen_16
               -> coe ("TLParen" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TRParen_18
               -> coe ("TRParen" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLBrace_20
               -> coe ("TLBrace" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TRBrace_22
               -> coe ("TRBrace" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TColon_24
               -> coe ("TColon" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TEquals_26
               -> coe ("TEquals" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TArrow_28
               -> coe ("TArrow" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TCaret1_30
               -> coe ("TCaret1" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TCaret0_32
               -> coe ("TCaret0" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TCaretW_34
               -> coe ("TCaretW" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLambda_36
               -> coe ("TLambda" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TComma_38
               -> coe ("TComma" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TSemicolon_40
               -> coe ("TSemicolon" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TAt_42
               -> coe ("TAt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TPipe_44
               -> coe ("TPipe" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TDot_46
               -> coe ("TDot" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TPlus_48
               -> coe ("TPlus" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TMinus_50
               -> coe ("TMinus" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TStar_52
               -> coe ("TStar" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TSlash_54
               -> coe ("TSlash" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TPercent_56
               -> coe ("TPercent" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TAmpersand_58
               -> coe ("TAmpersand" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLt_60
               -> coe ("TLt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TLe_62
               -> coe ("TLe" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TGt_64
               -> coe ("TGt" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TGe_66
               -> coe ("TGe" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TEqEq_68
               -> coe ("TEqEq" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TNeq_70
               -> coe ("TNeq" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TBang_72
               -> coe ("TBang" :: Data.Text.Text)
             MAlonzo.Code.Once.Parser.Token.C_TNewline_74
               -> coe d_showTokenPrefix_24 (coe v2)
             MAlonzo.Code.Once.Parser.Token.C_TEOF_76
               -> coe d_showTokenPrefix_24 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.knownTypeWord
d_knownTypeWord_32 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_knownTypeWord_32 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
         (coe
            MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
            (coe ("Unit" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
            (coe
               MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
               (coe ("Void" :: Data.Text.Text))))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                  (coe ("Int" :: Data.Text.Text))))
            (coe
               MAlonzo.Code.Data.Bool.Base.d__'8744'__30
               (coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                  (coe
                     MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                     (coe ("Float" :: Data.Text.Text))))
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                        (coe ("Buffer" :: Data.Text.Text))))
                  (coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                        (coe ("String" :: Data.Text.Text))))))))
-- Once.Parser.hasUpperTVar
d_hasUpperTVar_36 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_hasUpperTVar_36 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = d_hasUpperTVar_36 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe MAlonzo.Code.Once.Parser.Type.d_isUpperWord_6 (coe v4))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d_not_22
                             (coe d_knownTypeWord_32 (coe v4))))
                       (coe d_hasUpperTVar_36 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.tvarHint
d_tvarHint_44 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_tvarHint_44 v0
  = let v1 = d_hasUpperTVar_36 (coe v0) in
    coe
      (if coe v1
         then coe
                ("\n  hint: type variables must be lowercase (e.g. `a`, not `A`); uppercase names like `Int`/`Unit` are concrete types"
                 ::
                 Data.Text.Text)
         else coe ("" :: Data.Text.Text))
-- Once.Parser.parseStrict-at
d_parseStrict'45'at_56 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseStrict'45'at_56 v0 v1 v2
  = if coe v2
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Parse error: unexpected tokens remaining after last parsed decl (starting at: "
                 ::
                 Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_showTokenPrefix_24 (coe v0))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (")" :: Data.Text.Text) (d_tvarHint_44 (coe v0)))))
-- Once.Parser.parseStrict-pm
d_parseStrict'45'pm_66 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseStrict'45'pm_66 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    d_parseStrict'45'at_56 (coe v3) (coe v2)
                    (coe d_allTrailing_18 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe ("Parse error: module failed to parse" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.parseStrict
d_parseStrict_72 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseStrict_72 v0
  = coe
      d_parseStrict'45'pm_66
      (coe
         MAlonzo.Code.Once.Parser.Module.d_parseModule_380
         (coe
            MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_1038 (coe v0)))
-- Once.Parser.extractAliases
d_extractAliases_76 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extractAliases_76 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v1
        -> coe du_go_84 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_84 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_84 ~v0 v1 = du_go_84 v1
du_go_84 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_84 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = coe du_go_84 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6)))
                       (coe du_go_84 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo
d_FunInfo_96 = ()
data T_FunInfo_96
  = C_mkFunInfo_118 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    (Maybe MAlonzo.Code.Once.Type.T_Type_108)
                    (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                    MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 Bool
-- Once.Parser.FunInfo.funName
d_funName_108 ::
  T_FunInfo_96 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_funName_108 v0
  = case coe v0 of
      C_mkFunInfo_118 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funType
d_funType_110 ::
  T_FunInfo_96 -> Maybe MAlonzo.Code.Once.Type.T_Type_108
d_funType_110 v0
  = case coe v0 of
      C_mkFunInfo_118 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funAlloc
d_funAlloc_112 ::
  T_FunInfo_96 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_funAlloc_112 v0
  = case coe v0 of
      C_mkFunInfo_118 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funBody
d_funBody_114 ::
  T_FunInfo_96 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_funBody_114 v0
  = case coe v0 of
      C_mkFunInfo_118 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funIsPrimitive
d_funIsPrimitive_116 :: T_FunInfo_96 -> Bool
d_funIsPrimitive_116 v0
  = case coe v0 of
      C_mkFunInfo_118 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo
d_PolyFunInfo_120 = ()
data T_PolyFunInfo_120
  = C_mkPolyFunInfo_138 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Type.T_PolyType_240
                        (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                        MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
-- Once.Parser.PolyFunInfo.pfunName
d_pfunName_130 ::
  T_PolyFunInfo_120 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_pfunName_130 v0
  = case coe v0 of
      C_mkPolyFunInfo_138 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunType
d_pfunType_132 ::
  T_PolyFunInfo_120 -> MAlonzo.Code.Once.Type.T_PolyType_240
d_pfunType_132 v0
  = case coe v0 of
      C_mkPolyFunInfo_138 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunAlloc
d_pfunAlloc_134 ::
  T_PolyFunInfo_120 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_pfunAlloc_134 v0
  = case coe v0 of
      C_mkPolyFunInfo_138 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunBody
d_pfunBody_136 ::
  T_PolyFunInfo_120 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_pfunBody_136 v0
  = case coe v0 of
      C_mkPolyFunInfo_138 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.projectSig
d_projectSig_140 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_projectSig_140 v0 v1 v2
  = let v3 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48 (coe v0)
                   (coe MAlonzo.Code.Once.Type.d_extractGround_316 (coe v2) (coe v4)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Polymorphic signature not admissible here for `"
                    ::
                    Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("`: " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Once.Type.d_showPolyType_464 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (" \8212 primitives and type aliases must be ground. "
                                ::
                                Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("User `DFunDef`s with polymorphic sigs route into "
                                   ::
                                   Data.Text.Text)
                                  ("`PolyFunInfo` (plan 0.6 Phase C.1)." :: Data.Text.Text)))))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.PendingSig
d_PendingSig_166 :: ()
d_PendingSig_166 = erased
-- Once.Parser.EFResult
d_EFResult_168 :: ()
d_EFResult_168 = erased
-- Once.Parser.extractFunctions-consFun
d_extractFunctions'45'consFun_170 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_FunInfo_96 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'consFun_170 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v3))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions-consPoly
d_extractFunctions'45'consPoly_180 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_PolyFunInfo_120 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'consPoly_180 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions-go
d_extractFunctions'45'go_190 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'go_190 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1))
      (:) v3 v4
        -> let v5
                 = d_extractFunctions'45'go_190 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v6 v7
                  -> let v8 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v7) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                            -> let v10
                                     = MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                         (coe
                                            MAlonzo.Code.Once.Type.d_extractGround_316 (coe v7)
                                            (coe v9)) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe
                                           d_extractFunctions'45'go_190 (coe v0) (coe v4)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                       (coe v0)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.d_extractGround_316
                                                          (coe v7) (coe v9))))))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           d_extractFunctions'45'go_190 (coe v0) (coe v4)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                    (coe v7))))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                            -> coe
                                 d_extractFunctions'45'go_190 (coe v0) (coe v4)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v7))))
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
                                                             (coe
                                                                d_extractFunctions'45'consFun_170
                                                                (coe
                                                                   d_extractFunctions'45'go_190
                                                                   (coe v0) (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkFunInfo_118 (coe v6)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                      (coe v12))
                                                                   (coe v7) (coe v8)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                d_extractFunctions'45'go_190
                                                                (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
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
                                                             (coe
                                                                d_extractFunctions'45'consPoly_180
                                                                (coe
                                                                   d_extractFunctions'45'go_190
                                                                   (coe v0) (coe v4)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkPolyFunInfo_138 (coe v6)
                                                                   (coe v12) (coe v7) (coe v8)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                d_extractFunctions'45'go_190
                                                                (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v9
                                  = MAlonzo.Code.Once.TypeCheck.Principal.d_pgSchema_2112
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Principal.d_finishP_2090
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Principal.d_pInfer_1352
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Principal.d_projSchemas_932
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370)))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                            (coe v8) (coe (0 :: Integer))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                   -> coe
                                        d_extractFunctions'45'consPoly_180
                                        (coe
                                           d_extractFunctions'45'go_190 (coe v0) (coe v4) (coe v2))
                                        (coe
                                           C_mkPolyFunInfo_138 (coe v6) (coe v10) (coe v7) (coe v8))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe
                                        d_extractFunctions'45'consFun_170
                                        (coe
                                           d_extractFunctions'45'go_190 (coe v0) (coe v4) (coe v9))
                                        (coe
                                           C_mkFunInfo_118 (coe v6) (coe v9) (coe v7) (coe v8)
                                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v6 v7 v8 v9
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                         -> let v11 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v8) in
                            coe
                              (let v12
                                     = coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v10
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                            ("." :: Data.Text.Text) v6) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                      -> let v14
                                               = MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.d_extractGround_316
                                                      (coe v8) (coe v13)) in
                                         coe
                                           (coe
                                              d_extractFunctions'45'consFun_170
                                              (coe
                                                 d_extractFunctions'45'go_190 (coe v0) (coe v4)
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                              (coe
                                                 C_mkFunInfo_118
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    v10
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("." :: Data.Text.Text) v6))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                    (coe v14))
                                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       v10
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("." :: Data.Text.Text) v6)))
                                                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                      -> coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("Polymorphic signature not admissible here for `"
                                               ::
                                               Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v12
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("`: " :: Data.Text.Text)
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (MAlonzo.Code.Once.Type.d_showPolyType_464
                                                          (coe v8))
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          (" \8212 primitives and type aliases must be ground. "
                                                           ::
                                                           Data.Text.Text)
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             ("User `DFunDef`s with polymorphic sigs route into "
                                                              ::
                                                              Data.Text.Text)
                                                             ("`PolyFunInfo` (plan 0.6 Phase C.1)."
                                                              ::
                                                              Data.Text.Text)))))))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v10 = MAlonzo.Code.Once.Type.d_isGround_432 (coe v8) in
                            coe
                              (case coe v10 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                   -> let v12
                                            = MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48
                                                (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Type.d_extractGround_316
                                                   (coe v8) (coe v11)) in
                                      coe
                                        (coe
                                           d_extractFunctions'45'consFun_170
                                           (coe
                                              d_extractFunctions'45'go_190 (coe v0) (coe v4)
                                              (coe v7))
                                           (coe
                                              C_mkFunInfo_118 (coe v6)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                 (coe v12))
                                              (coe v7)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v6))
                                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("Polymorphic signature not admissible here for `"
                                            ::
                                            Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v6
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("`: " :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    (MAlonzo.Code.Once.Type.d_showPolyType_464
                                                       (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       (" \8212 primitives and type aliases must be ground. "
                                                        ::
                                                        Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          ("User `DFunDef`s with polymorphic sigs route into "
                                                           ::
                                                           Data.Text.Text)
                                                          ("`PolyFunInfo` (plan 0.6 Phase C.1)."
                                                           ::
                                                           Data.Text.Text)))))))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.nameElem
d_nameElem_454 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_nameElem_454 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v5)
                       else coe seq (coe v6) (coe d_nameElem_454 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.namesDistinct
d_namesDistinct_478 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_namesDistinct_478 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe d_nameElem_454 (coe v1) (coe v2)))
             (coe d_namesDistinct_478 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.allIdentContinue
d_allIdentContinue_484 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allIdentContinue_484 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentContinue_12 (coe v1))
             (coe d_allIdentContinue_484 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.validCharsB
d_validCharsB_490 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_validCharsB_490 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v1))
             (coe d_allIdentContinue_484 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.validIdentB
d_validIdentB_496 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_validIdentB_496 v0
  = coe
      d_validCharsB_490
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Parser.allValidIdentB
d_allValidIdentB_500 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_allValidIdentB_500 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_validIdentB_496 (coe v1))
             (coe d_allValidIdentB_500 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.emittedNames-cons
d_emittedNames'45'cons_506 ::
  Bool ->
  T_FunInfo_96 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedNames'45'cons_506 v0 v1 v2
  = if coe v0
      then coe v2
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_funName_108 (coe v1)) (coe v2)
-- Once.Parser.emittedNames
d_emittedNames_516 ::
  [T_FunInfo_96] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedNames_516 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_emittedNames'45'cons_506 (coe d_funIsPrimitive_116 (coe v1))
             (coe v1) (coe d_emittedNames_516 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.distinctOrErr
d_distinctOrErr_522 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_distinctOrErr_522 v0 v1
  = if coe v0
      then coe v1
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                ("ill-formed top-level definition name (duplicate or not an identifier)"
                 ::
                 Data.Text.Text))
-- Once.Parser.guardDistinct
d_guardDistinct_526 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_guardDistinct_526 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    d_distinctOrErr_522
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_namesDistinct_478 (coe du_nms_538 (coe v2)))
                       (coe d_allValidIdentB_500 (coe du_nms_538 (coe v2))))
                    (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.nms
d_nms_538 ::
  [T_FunInfo_96] ->
  [T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nms_538 v0 ~v1 = du_nms_538 v0
du_nms_538 ::
  [T_FunInfo_96] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_nms_538 v0 = coe d_emittedNames_516 (coe v0)
-- Once.Parser.extractFunctions
d_extractFunctions_540 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions_540 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v2
        -> coe
             d_guardDistinct_526
             (coe
                d_extractFunctions'45'go_190 (coe v0) (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
