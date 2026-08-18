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

module MAlonzo.Code.Once.Adequacy.FrontEndBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Adequacy.LexerBridge
import qualified MAlonzo.Code.Once.Grammar.DeclBridge
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Adequacy.FrontEndBridge.ParsesDecls
d_ParsesDecls_6 a0 a1 a2 = ()
data T_ParsesDecls_6
  = C_pds'45'noskip_10 |
    C_pds'45'stop_18 [MAlonzo.Code.Once.Parser.Token.T_Token_6] |
    C_pds'45'cons_34 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                     MAlonzo.Code.Once.Grammar.DeclBridge.T_ParsesDecl_6 T_ParsesDecls_6
-- Once.Adequacy.FrontEndBridge.SkBnd
d_SkBnd_40 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_SkBnd_40 = erased
-- Once.Adequacy.FrontEndBridge.sound-declsWF
d_sound'45'declsWF_54 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> T_ParsesDecls_6
d_sound'45'declsWF_54 v0 ~v1 = du_sound'45'declsWF_54 v0
du_sound'45'declsWF_54 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_ParsesDecls_6
du_sound'45'declsWF_54 v0
  = coe
      du_sound'45'pdwf'45'sk_68
      (coe MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278 (coe v0))
-- Once.Adequacy.FrontEndBridge.sound-pdwf-sk
d_sound'45'pdwf'45'sk_68 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ParsesDecls_6
d_sound'45'pdwf'45'sk_68 ~v0 ~v1 v2 ~v3 ~v4
  = du_sound'45'pdwf'45'sk_68 v2
du_sound'45'pdwf'45'sk_68 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_ParsesDecls_6
du_sound'45'pdwf'45'sk_68 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> coe
                    du_sound'45'pdwf'45'dc_88 (coe v3)
                    (coe MAlonzo.Code.Once.Parser.Module.d_parseDeclB_146 (coe v3))
                    (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_pds'45'noskip_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FrontEndBridge.sound-pdwf-dc
d_sound'45'pdwf'45'dc_88 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ParsesDecls_6
d_sound'45'pdwf'45'dc_88 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7
  = du_sound'45'pdwf'45'dc_88 v2 v4 v6
du_sound'45'pdwf'45'dc_88 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_ParsesDecls_6
du_sound'45'pdwf'45'dc_88 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           C_pds'45'cons_34 v2 v0 v6
                           (coe
                              MAlonzo.Code.Once.Grammar.DeclBridge.du_sound'45'decl_68 (coe v0))
                           (coe du_sound'45'declsWF_54 (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_pds'45'stop_18 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FrontEndBridge.sound-decls
d_sound'45'decls_154 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ParsesDecls_6
d_sound'45'decls_154 v0 ~v1 ~v2 ~v3 = du_sound'45'decls_154 v0
du_sound'45'decls_154 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_ParsesDecls_6
du_sound'45'decls_154 v0 = coe du_sound'45'declsWF_54 (coe v0)
-- Once.Adequacy.FrontEndBridge.complete-declsWF
d_complete'45'declsWF_174 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  T_ParsesDecls_6 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'declsWF_174 ~v0 v1 v2 ~v3 v4
  = du_complete'45'declsWF_174 v1 v2 v4
du_complete'45'declsWF_174 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDecls_6 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'declsWF_174 v0 v1 v2
  = coe du_complete'45'pdwf'45'sk_192 (coe v0) (coe v1) (coe v2)
-- Once.Adequacy.FrontEndBridge.complete-pdwf-sk
d_complete'45'pdwf'45'sk_192 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDecls_6 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_complete'45'pdwf'45'sk_192 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_complete'45'pdwf'45'sk_192 v5 v6 v7
du_complete'45'pdwf'45'sk_192 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDecls_6 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_complete'45'pdwf'45'sk_192 v0 v1 v2
  = case coe v2 of
      C_pds'45'noskip_10
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      C_pds'45'stop_18 v4
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      C_pds'45'cons_34 v4 v5 v7 v11 v12
        -> case coe v0 of
             (:) v13 v14
               -> let v15
                        = MAlonzo.Code.Once.Grammar.DeclBridge.d_complete'45'decl_312
                            (coe v5) (coe v13) (coe v7) (coe v11) in
                  coe
                    (coe
                       seq (coe v15)
                       (coe du_complete'45'declsWF_174 (coe v14) (coe v1) (coe v12)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FrontEndBridge.complete-decls
d_complete'45'decls_322 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDecls_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'decls_322 = erased
-- Once.Adequacy.FrontEndBridge.ParsesModule
d_ParsesModule_352 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParsesModule_352 = erased
-- Once.Adequacy.FrontEndBridge.parseDecls-total
d_parseDecls'45'total_366 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseDecls'45'total_366 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308 (coe v0)
              (coe MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278 (coe v0))
              (\ v1 v2 v3 ->
                 coe
                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                   (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) erased)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FrontEndBridge.complete-module
d_complete'45'module_386 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_ParsesDecls_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete'45'module_386 = erased
-- Once.Adequacy.FrontEndBridge.sound-module
d_sound'45'module_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ParsesDecls_6
d_sound'45'module_404 v0 ~v1 ~v2 ~v3 = du_sound'45'module_404 v0
du_sound'45'module_404 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_ParsesDecls_6
du_sound'45'module_404 v0 = coe du_sound'45'decls_154 (coe v0)
-- Once.Adequacy.FrontEndBridge.ParsesText
d_ParsesText_436 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> ()
d_ParsesText_436 = erased
-- Once.Adequacy.FrontEndBridge.parseStrict-complete
d_parseStrict'45'complete_450 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_parseStrict'45'complete_450 = erased
-- Once.Adequacy.FrontEndBridge.parseModule-total-at
d_parseModule'45'total'45'at_474 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseModule'45'total'45'at_474 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                 (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0))
                 (coe
                    MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                    (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0)))
                 (\ v1 v2 v3 ->
                    coe
                      MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                      (coe
                         MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0)))) in
    coe
      (let v2
             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0))
                       (coe
                          MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                          (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0)))
                       (\ v2 v3 v4 ->
                          coe
                            MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                            (coe
                               MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0))))) in
       coe
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v1))
            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased)))
-- Once.Adequacy.FrontEndBridge.parseStrict-sound
d_parseStrict'45'sound_496 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseStrict'45'sound_496 v0 ~v1 ~v2
  = du_parseStrict'45'sound_496 v0
du_parseStrict'45'sound_496 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseStrict'45'sound_496 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe
                    MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                    (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                       (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0)))
                    (\ v1 v2 v3 ->
                       coe
                         MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                         (coe
                            MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0))))) in
    coe
      (coe
         du_go_530 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Parser.d_allTrailing_18 (coe v1)))
-- Once.Adequacy.FrontEndBridge._.eqAt
d_eqAt_524 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqAt_524 = erased
-- Once.Adequacy.FrontEndBridge._.go
d_go_530 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_530 v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_go_530 v0 v2 v6
du_go_530 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_530 v0 v1 v2
  = coe du_goB_542 (coe v0) (coe v1) (coe v2) erased
-- Once.Adequacy.FrontEndBridge._._.goB
d_goB_542 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_goB_542 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10
  = du_goB_542 v0 v2 v8 v10
du_goB_542 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_goB_542 v0 v1 v2 v3
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe
                  MAlonzo.Code.Once.Adequacy.LexerBridge.d_lexer'45'sound_918
                  (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     du_sound'45'module_404
                     (coe MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_908 (coe v0)))
                  (coe v3)))))
