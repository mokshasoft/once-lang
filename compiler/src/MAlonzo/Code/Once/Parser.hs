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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Poly
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.parse
d_parse_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122
d_parse_4 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_128
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Parser.Module.d_r_370
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_1022 (coe v0)))) in
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
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
               (coe
                  MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                  (coe ("Float" :: Data.Text.Text))))))
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122 ->
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
            MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_1022 (coe v0)))
-- Once.Parser.FunInfo
d_FunInfo_76 = ()
data T_FunInfo_76
  = C_mkFunInfo_94 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   (Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8)
                   MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 Bool
-- Once.Parser.FunInfo.funName
d_funName_86 ::
  T_FunInfo_76 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_funName_86 v0
  = case coe v0 of
      C_mkFunInfo_94 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funType
d_funType_88 ::
  T_FunInfo_76 -> Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_funType_88 v0
  = case coe v0 of
      C_mkFunInfo_94 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funBody
d_funBody_90 ::
  T_FunInfo_76 -> MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_funBody_90 v0
  = case coe v0 of
      C_mkFunInfo_94 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funIsPrimitive
d_funIsPrimitive_92 :: T_FunInfo_76 -> Bool
d_funIsPrimitive_92 v0
  = case coe v0 of
      C_mkFunInfo_94 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo
d_PolyFunInfo_96 = ()
data T_PolyFunInfo_96
  = C_mkPolyFunInfo_110 MAlonzo.Code.Agda.Builtin.String.T_String_6
                        MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
                        MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
-- Once.Parser.PolyFunInfo.pfunName
d_pfunName_104 ::
  T_PolyFunInfo_96 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_pfunName_104 v0
  = case coe v0 of
      C_mkPolyFunInfo_110 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunType
d_pfunType_106 ::
  T_PolyFunInfo_96 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10
d_pfunType_106 v0
  = case coe v0 of
      C_mkPolyFunInfo_110 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.PolyFunInfo.pfunBody
d_pfunBody_108 ::
  T_PolyFunInfo_96 -> MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68
d_pfunBody_108 v0
  = case coe v0 of
      C_mkPolyFunInfo_110 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Entry
d_Entry_112 = ()
data T_Entry_112
  = C_e'45'fun_114 T_FunInfo_76 | C_e'45'poly_116 T_PolyFunInfo_96
-- Once.Parser.funsOf
d_funsOf_118 :: [T_Entry_112] -> [T_FunInfo_76]
d_funsOf_118 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             C_e'45'fun_114 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                    (coe d_funsOf_118 (coe v2))
             C_e'45'poly_116 v3 -> coe d_funsOf_118 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.polysOf
d_polysOf_126 :: [T_Entry_112] -> [T_PolyFunInfo_96]
d_polysOf_126 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             C_e'45'fun_114 v3 -> coe d_polysOf_126 (coe v2)
             C_e'45'poly_116 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                    (coe d_polysOf_126 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.honestSig
d_honestSig_136 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_honestSig_136 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Signature `" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` : " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Once.Type.d_showType_36
                            (coe (0 :: Integer)) (coe v1))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (" hides an effect: a SigOp " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("returning Unit emits and one returning Void halts, so its arrow must be Eff "
                                ::
                                Data.Text.Text)
                               ("(a bare Unit/Void constant is written Eff Unit Unit)"
                                ::
                                Data.Text.Text)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.projectSig
d_projectSig_146 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_projectSig_146 v0 v1
  = let v2 = MAlonzo.Code.Once.Type.d_isGround_98 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe
                d_honestSig_136 (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.Poly.d_extractGround_54 (coe (0 :: Integer))
                   (coe v1) (coe v3))
                (coe
                   MAlonzo.Code.Once.Type.Honest.d_honest'63'_200
                   (coe
                      MAlonzo.Code.Once.Type.Poly.d_extractGround_54 (coe (0 :: Integer))
                      (coe v1) (coe v3)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Polymorphic signature not admissible here for `"
                    ::
                    Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("`: " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Once.Type.d_showPolyType_134 (coe v1))
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
  T_FunInfo_76 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'consFun_170 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe C_e'45'fun_114 (coe v1)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions-consPoly
d_extractFunctions'45'consPoly_178 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'consPoly_178 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   C_e'45'poly_116
                   (coe C_mkPolyFunInfo_110 (coe v1) (coe v2) (coe v3)))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.danglingSig
d_danglingSig_190 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_danglingSig_190 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("The signature of `" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         ("` is not followed by its definition" :: Data.Text.Text))
-- Once.Parser.extractFunctions-go
d_extractFunctions'45'go_194 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'go_194 v0 v1
  = case coe v0 of
      []
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_danglingSig_190 (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v2 v3
        -> let v4
                 = case coe v1 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                       -> case coe v4 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                              -> coe
                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                   (coe d_danglingSig_190 (coe v5))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe d_extractFunctions'45'go_194 (coe v3) (coe v1)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v5 v6
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                     (coe d_danglingSig_190 (coe v8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v7 = MAlonzo.Code.Once.Type.d_isGround_98 (coe v6) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                                   -> let v9
                                            = MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                                (coe
                                                   MAlonzo.Code.Once.Type.Poly.d_extractGround_54
                                                   (coe (0 :: Integer)) (coe v6) (coe v8)) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                             -> coe
                                                  d_extractFunctions'45'go_194 (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                           (coe
                                                              MAlonzo.Code.Once.Type.Poly.d_extractGround_54
                                                              (coe (0 :: Integer)) (coe v6)
                                                              (coe v8)))))
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> coe
                                                  d_extractFunctions'45'go_194 (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                           (coe v6))))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                                   -> coe
                                        d_extractFunctions'45'go_194 (coe v3)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                              (coe
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                 (coe v6))))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v5 v6
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> case coe v9 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                       -> let v11
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v11 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                       (coe v8) (coe v5)) in
                                          coe
                                            (case coe v11 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                 -> if coe v12
                                                      then coe
                                                             seq (coe v13)
                                                             (coe
                                                                d_extractFunctions'45'consFun_170
                                                                (coe
                                                                   d_extractFunctions'45'go_194
                                                                   (coe v3)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe
                                                                   C_mkFunInfo_94 (coe v5)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                      (coe v10))
                                                                   (coe v6)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                                                      else coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                (coe d_danglingSig_190 (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                       -> let v11
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v11 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                       (coe v8) (coe v5)) in
                                          coe
                                            (case coe v11 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                 -> if coe v12
                                                      then coe
                                                             seq (coe v13)
                                                             (coe
                                                                d_extractFunctions'45'consPoly_178
                                                                (coe
                                                                   d_extractFunctions'45'go_194
                                                                   (coe v3)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                                                (coe v5) (coe v10) (coe v6))
                                                      else coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                (coe d_danglingSig_190 (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              du_extractFunctions'45'sigless_198 (coe v5) (coe v6) (coe v3)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v5 v6
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> case coe v7 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                -> coe
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                     (coe d_danglingSig_190 (coe v8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> let v7 = MAlonzo.Code.Once.Type.d_isGround_98 (coe v6) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                                   -> let v9
                                            = d_honestSig_136
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Once.Type.Poly.d_extractGround_54
                                                   (coe (0 :: Integer)) (coe v6) (coe v8))
                                                (coe
                                                   MAlonzo.Code.Once.Type.Honest.d_honest'63'_200
                                                   (coe
                                                      MAlonzo.Code.Once.Type.Poly.d_extractGround_54
                                                      (coe (0 :: Integer)) (coe v6) (coe v8))) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> coe v9
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                             -> coe
                                                  d_extractFunctions'45'consFun_170
                                                  (coe
                                                     d_extractFunctions'45'go_194 (coe v3) (coe v1))
                                                  (coe
                                                     C_mkFunInfo_94 (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                        (coe v10))
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70
                                                        (coe v5))
                                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("Polymorphic signature not admissible here for `"
                                            ::
                                            Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v5
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("`: " :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    (MAlonzo.Code.Once.Type.d_showPolyType_134
                                                       (coe v6))
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
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions-sigless
d_extractFunctions'45'sigless_198 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions'45'sigless_198 v0 v1 v2 ~v3
  = du_extractFunctions'45'sigless_198 v0 v1 v2
du_extractFunctions'45'sigless_198 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_extractFunctions'45'sigless_198 v0 v1 v2
  = coe
      d_extractFunctions'45'consFun_170
      (coe
         d_extractFunctions'45'go_194 (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe
         C_mkFunInfo_94 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Once.Parser.namesDistinct
d_namesDistinct_374 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_namesDistinct_374 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.du_allPairs'63'_110
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
                 (coe
                    MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v1)
                    (coe v2))))
         (coe v0))
-- Once.Parser.allIdentContinue
d_allIdentContinue_382 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allIdentContinue_382 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentContinue_12 (coe v1))
             (coe d_allIdentContinue_382 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.validCharsB
d_validCharsB_388 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_validCharsB_388 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isIdentStart_8 (coe v1))
             (coe d_allIdentContinue_382 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.allOpNameChars
d_allOpNameChars_394 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_allOpNameChars_394 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe MAlonzo.Code.Once.Parser.Lexer.d_isOpNameChar_18 (coe v1))
             (coe d_allOpNameChars_394 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.opCharsB
d_opCharsB_400 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> Bool
d_opCharsB_400 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2 -> coe d_allOpNameChars_394 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.validNameB
d_validNameB_406 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_validNameB_406 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         d_validCharsB_388
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
      (coe
         d_opCharsB_400
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0))
-- Once.Parser.allValidNameB
d_allValidNameB_410 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_allValidNameB_410 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe d_validNameB_406 (coe v1)) (coe d_allValidNameB_410 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.emittedNames-cons
d_emittedNames'45'cons_416 ::
  Bool ->
  T_FunInfo_76 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedNames'45'cons_416 v0 v1 v2
  = if coe v0
      then coe v2
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_funName_86 (coe v1)) (coe v2)
-- Once.Parser.emittedNames
d_emittedNames_426 ::
  [T_FunInfo_76] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedNames_426 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_emittedNames'45'cons_416 (coe d_funIsPrimitive_92 (coe v1))
             (coe v1) (coe d_emittedNames_426 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.distinctOrErr
d_distinctOrErr_432 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_distinctOrErr_432 v0 v1 v2
  = if coe v0
      then coe v2
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1)
-- Once.Parser.firstDuplicate
d_firstDuplicate_438 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_firstDuplicate_438 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_duplicateOr_440
             (coe
                MAlonzo.Code.Data.Bool.ListAction.du_any_14
                (coe
                   (\ v3 ->
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                        (coe
                           MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v1)
                           (coe v3))))
                (coe v2))
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.duplicateOr
d_duplicateOr_440 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_duplicateOr_440 v0 v1 v2
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      else coe d_firstDuplicate_438 (coe v2)
-- Once.Parser.firstInvalid
d_firstInvalid_452 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_firstInvalid_452 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_invalidOr_454 (coe d_validNameB_406 (coe v1)) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.invalidOr
d_invalidOr_454 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_invalidOr_454 v0 v1 v2
  = if coe v0
      then coe d_firstInvalid_452 (coe v2)
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
-- Once.Parser.entryNameOf
d_entryNameOf_464 ::
  T_Entry_112 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_entryNameOf_464 v0
  = case coe v0 of
      C_e'45'fun_114 v1 -> coe d_funName_86 (coe v1)
      C_e'45'poly_116 v1 -> coe d_pfunName_104 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.guardMsg
d_guardMsg_470 ::
  [T_Entry_112] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_guardMsg_470 v0
  = coe
      d_dupMsg_482 (coe v0)
      (coe
         d_firstDuplicate_438
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22 (coe d_entryNameOf_464)
            (coe v0)))
-- Once.Parser._.invalidMsg
d_invalidMsg_478 ::
  [T_Entry_112] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_invalidMsg_478 ~v0 v1 = du_invalidMsg_478 v1
du_invalidMsg_478 ::
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_invalidMsg_478 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("`" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                ("` is not an identifier or an operator name" :: Data.Text.Text))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             ("ill-formed top-level name (duplicate or not an identifier)"
              ::
              Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.dupMsg
d_dupMsg_482 ::
  [T_Entry_112] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_dupMsg_482 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("`" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                ("` is declared more than once: definitions and `signature` declarations share one namespace, and each name is declared once"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             du_invalidMsg_478
             (coe
                d_firstInvalid_452
                (coe d_emittedNames_426 (coe d_funsOf_118 (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.guardDistinct
d_guardDistinct_486 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_guardDistinct_486 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             d_distinctOrErr_432
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                   (coe
                      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                      (coe d_namesDistinct_374 (coe d_nms_496 (coe v1)))
                      (coe d_allValidNameB_410 (coe d_nms_496 (coe v1))))
                   (coe
                      d_namesDistinct_374
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe d_nms_496 (coe v1))
                         (coe
                            MAlonzo.Code.Data.List.Base.du_map_22
                            (coe (\ v2 -> d_pfunName_104 (coe v2)))
                            (coe d_polysOf_126 (coe v1))))))
                (coe
                   d_namesDistinct_374
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22 (coe d_entryNameOf_464)
                      (coe v1))))
             (coe d_guardMsg_470 (coe v1)) (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.nms
d_nms_496 ::
  [T_Entry_112] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_nms_496 v0 = coe d_emittedNames_426 (coe d_funsOf_118 (coe v0))
-- Once.Parser.sigsAdjacent
d_sigsAdjacent_498 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sigsAdjacent_498 v0 v1
  = case coe v0 of
      []
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_danglingSig_190 (coe v2))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v2 v3
        -> let v4
                 = case coe v1 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                       -> coe
                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                            (coe d_danglingSig_190 (coe v4))
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe d_sigsAdjacent_498 (coe v3) (coe v1)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DTypeSig_112 v5 v6
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                              (coe d_danglingSig_190 (coe v7))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              d_sigsAdjacent_498 (coe v3)
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DFunDef_114 v5 v6
                  -> case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> coe
                              du_sigsAdjacent'45'def_504 (coe v7)
                              (coe
                                 MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v7)
                                 (coe v5))
                              (coe v3)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe d_sigsAdjacent_498 (coe v3) (coe v1)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.sigsAdjacent-def
d_sigsAdjacent'45'def_504 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sigsAdjacent'45'def_504 v0 ~v1 v2 v3
  = du_sigsAdjacent'45'def_504 v0 v2 v3
du_sigsAdjacent'45'def_504 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sigsAdjacent'45'def_504 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       d_sigsAdjacent_498 (coe v2)
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe d_danglingSig_190 (coe v0)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.ownSigs
d_ownSigs_544 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110]
d_ownSigs_544 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_ownSigs_544 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                       (coe d_ownSigs_544 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.importedSigs
d_importedSigs_554 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110]
d_importedSigs_554 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 (coe v3)
                       (coe v4))
                    (coe d_importedSigs_554 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.nonSigs
d_nonSigs_562 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110]
d_nonSigs_562 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                     (coe d_nonSigs_562 (coe v2)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_DSignature_116 v4 v5
                  -> coe d_nonSigs_562 (coe v2)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.sigsFirst
d_sigsFirst_570 ::
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Spec.Surface.Syntax.T_Decl_110]
d_sigsFirst_570 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe d_ownSigs_544 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe d_importedSigs_554 (coe v1)) (coe d_nonSigs_562 (coe v0)))
-- Once.Parser.thenExtract
d_thenExtract_576 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_thenExtract_576 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions
d_extractFunctions_582 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_extractFunctions_582 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_resolved_18 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_mkModule_128 v3
               -> coe
                    d_guardDistinct_486
                    (coe
                       d_thenExtract_576
                       (coe
                          d_sigsAdjacent_498 (coe v3)
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                       (coe
                          d_extractFunctions'45'go_194
                          (coe d_sigsFirst_570 (coe v3) (coe v2))
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
