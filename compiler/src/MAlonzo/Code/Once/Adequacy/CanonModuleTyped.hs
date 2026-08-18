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

module MAlonzo.Code.Once.Adequacy.CanonModuleTyped where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CanonAllFuns
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve

-- Once.Adequacy.CanonModuleTyped.canonModule
d_canonModule_6 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_canonModule_6 v0
  = coe
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_canonDecl_534
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_314
               (coe v0))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe v0))
-- Once.Adequacy.CanonModuleTyped.extractAliases-canonB
d_extractAliases'45'canonB_14 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractAliases'45'canonB_14 = erased
-- Once.Adequacy.CanonModuleTyped.extractAliases-canon
d_extractAliases'45'canon_68 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractAliases'45'canon_68 = erased
-- Once.Adequacy.CanonModuleTyped.collectSigEffects-canonB
d_collectSigEffects'45'canonB_76 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_collectSigEffects'45'canonB_76 = erased
-- Once.Adequacy.CanonModuleTyped.collectSigEffects-canon
d_collectSigEffects'45'canon_160 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_collectSigEffects'45'canon_160 = erased
-- Once.Adequacy.CanonModuleTyped.emittedNames-canon
d_emittedNames'45'canon_168 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_emittedNames'45'canon_168 = erased
-- Once.Adequacy.CanonModuleTyped.guardDistinct-canon
d_guardDistinct'45'canon_202 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guardDistinct'45'canon_202 = erased
-- Once.Adequacy.CanonModuleTyped.extractFunctions-canon
d_extractFunctions'45'canon_242 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractFunctions'45'canon_242 = erased
-- Once.Adequacy.CanonModuleTyped._.peel
d_peel_256 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_peel_256 = erased
-- Once.Adequacy.CanonModuleTyped.module-typed-canon-aux
d_module'45'typed'45'canon'45'aux_274 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_module'45'typed'45'canon'45'aux_274 v0 v1 ~v2 v3
  = du_module'45'typed'45'canon'45'aux_274 v0 v1 v3
du_module'45'typed'45'canon'45'aux_274 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
du_module'45'typed'45'canon'45'aux_274 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Adequacy.CanonAllFuns.du_AllFunsTyped'45'transport_790
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_314
                       (coe v0))
                    (coe v5)
                    (coe MAlonzo.Code.Once.Compile.d_collectSigEffects_498 (coe v0))
                    (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonModuleTyped.module-typed-canon
d_module'45'typed'45'canon_302 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  AgdaAny -> AgdaAny
d_module'45'typed'45'canon_302 v0 v1
  = coe
      du_module'45'typed'45'canon'45'aux_274 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe
            MAlonzo.Code.Once.Parser.d_extractAliases_76
            (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v0)))
         (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v0)))
      (coe v1)
-- Once.Adequacy.CanonModuleTyped.module-typed-and-valid-aux
d_module'45'typed'45'and'45'valid'45'aux_316 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_module'45'typed'45'and'45'valid'45'aux_316 v0 v1 ~v2 v3 v4
  = du_module'45'typed'45'and'45'valid'45'aux_316 v0 v1 v3 v4
du_module'45'typed'45'and'45'valid'45'aux_316 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_module'45'typed'45'and'45'valid'45'aux_316 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Adequacy.CanonAllFuns.du_AllFunsTyped'45'transport_790
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe
                                 MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_314
                                 (coe v0))
                              (coe v6)
                              (coe MAlonzo.Code.Once.Compile.d_collectSigEffects_498 (coe v0))
                              (coe v5) (coe v2))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CanonAllFuns.du_AllMainEffUU'45'transport_836
                                 (coe v5) (coe v2) (coe v7))
                              (coe
                                 MAlonzo.Code.Once.Adequacy.CanonAllFuns.du_MainExists'45'transport_884
                                 (coe v5) (coe v2) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonModuleTyped.module-typed-and-valid
d_module'45'typed'45'and'45'valid_354 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_module'45'typed'45'and'45'valid_354 v0 v1 v2
  = coe
      du_module'45'typed'45'and'45'valid'45'aux_316 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe
            MAlonzo.Code.Once.Parser.d_extractAliases_76
            (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v0)))
         (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v0)))
      (coe v1) (coe v2)
