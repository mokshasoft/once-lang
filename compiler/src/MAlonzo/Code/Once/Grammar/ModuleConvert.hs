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

module MAlonzo.Code.Once.Grammar.ModuleConvert where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Grammar
import qualified MAlonzo.Code.Once.Grammar.ConcreteDec
import qualified MAlonzo.Code.Once.Grammar.Convert
import qualified MAlonzo.Code.Once.Grammar.ExprConvert
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Type

-- Once.Grammar.ModuleConvert.gtypeToPolyType
d_gtypeToPolyType_6 ::
  MAlonzo.Code.Once.Grammar.T_GType_8 ->
  MAlonzo.Code.Once.Type.T_PolyType_240
d_gtypeToPolyType_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_12
        -> coe MAlonzo.Code.Once.Type.C_PUnit_250
      MAlonzo.Code.Once.Grammar.C_TVoid_14
        -> coe MAlonzo.Code.Once.Type.C_PVoid_252
      MAlonzo.Code.Once.Grammar.C_TInt_16
        -> coe MAlonzo.Code.Once.Type.C_PInt_266
      MAlonzo.Code.Once.Grammar.C_TFloat_18
        -> coe MAlonzo.Code.Once.Type.C_PFloat_268
      MAlonzo.Code.Once.Grammar.C_TBuffer_20
        -> coe MAlonzo.Code.Once.Type.C_PBuffer_272
      MAlonzo.Code.Once.Grammar.C_TString_22
        -> coe MAlonzo.Code.Once.Type.C_PStr_270
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__24 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__258
             (coe d_gtypeToPolyType_6 (coe v1)) (coe v2)
             (coe d_gtypeToPolyType_6 (coe v3))
      MAlonzo.Code.Once.Grammar.C__'8855'__26 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'42'__254
             (coe d_gtypeToPolyType_6 (coe v1))
             (coe d_gtypeToPolyType_6 (coe v2))
      MAlonzo.Code.Once.Grammar.C__'8853'__28 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'43'__256
             (coe d_gtypeToPolyType_6 (coe v1))
             (coe d_gtypeToPolyType_6 (coe v2))
      MAlonzo.Code.Once.Grammar.C_TEff_30 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C_PEff_260
             (coe d_gtypeToPolyType_6 (coe v1))
             (coe d_gtypeToPolyType_6 (coe v2))
      MAlonzo.Code.Once.Grammar.C_GMu_32 v1
        -> coe
             MAlonzo.Code.Once.Type.C_Pμ'45'type_262
             (coe d_gtypeToPolyFunctor_8 (coe v1))
      MAlonzo.Code.Once.Grammar.C_TVar_34 v1
        -> coe MAlonzo.Code.Once.Type.C_PTVar_274 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.gtypeToPolyFunctor
d_gtypeToPolyFunctor_8 ::
  MAlonzo.Code.Once.Grammar.T_GFunctor_10 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_238
d_gtypeToPolyFunctor_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_GFK_36 v1
        -> coe
             MAlonzo.Code.Once.Type.C_PK_242 (coe d_gtypeToPolyType_6 (coe v1))
      MAlonzo.Code.Once.Grammar.C_GFId_38
        -> coe MAlonzo.Code.Once.Type.C_PId_244
      MAlonzo.Code.Once.Grammar.C_GFSum_40 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'8853'__246
             (coe d_gtypeToPolyFunctor_8 (coe v1))
             (coe d_gtypeToPolyFunctor_8 (coe v2))
      MAlonzo.Code.Once.Grammar.C_GFProd_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'8855'__248
             (coe d_gtypeToPolyFunctor_8 (coe v1))
             (coe d_gtypeToPolyFunctor_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.wrapParams
d_wrapParams_42 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Grammar.T_GExpr_82 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_82
d_wrapParams_42 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Once.Grammar.C_ELam_94 (coe v2)
             (coe d_wrapParams_42 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.gdeclToDecl
d_gdeclToDecl_52 ::
  MAlonzo.Code.Once.Grammar.T_GDecl_114 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20
d_gdeclToDecl_52 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_DTypeSig_116 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_22 (coe v1)
                (coe d_gtypeToPolyType_6 (coe v2)))
      MAlonzo.Code.Once.Grammar.C_DFunDef_118 v1 v2 v3
        -> let v4
                 = MAlonzo.Code.Once.Grammar.ConcreteDec.d_concrete'63'_98
                     (coe d_wrapParams_42 (coe v2) (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                             (coe d_wrapParams_42 (coe v2) (coe v3)) (coe v5)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_DSignature_120 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_26 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe d_gtypeToPolyType_6 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_DTypeAlias_122 v1 v2 v3
        -> let v4
                 = MAlonzo.Code.Once.Grammar.Convert.d_gtypeToType_6 (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_28 (coe v1)
                          (coe v2) (coe v5))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_DImport_124 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_30
                (coe
                   MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_18 (coe v1)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.mapDecls
d_mapDecls_114 ::
  [MAlonzo.Code.Once.Grammar.T_GDecl_114] ->
  Maybe [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20]
d_mapDecls_114 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
      (:) v1 v2
        -> let v3 = d_gdeclToDecl_52 (coe v1) in
           coe
             (let v4 = d_mapDecls_114 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v6))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.gmoduleToModule
d_gmoduleToModule_136 ::
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_gmoduleToModule_136 v0
  = let v1
          = d_mapDecls_114
              (coe MAlonzo.Code.Once.Grammar.d_decls_130 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
