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
  MAlonzo.Code.Once.Type.T_PolyType_254
d_gtypeToPolyType_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_TUnit_12
        -> coe MAlonzo.Code.Once.Type.C_PUnit_264
      MAlonzo.Code.Once.Grammar.C_TVoid_14
        -> coe MAlonzo.Code.Once.Type.C_PVoid_266
      MAlonzo.Code.Once.Grammar.C_TInt_16
        -> coe MAlonzo.Code.Once.Type.C_PInt_280
      MAlonzo.Code.Once.Grammar.C_TFloat_18
        -> coe MAlonzo.Code.Once.Type.C_PFloat_282
      MAlonzo.Code.Once.Grammar.C__'8658''91'_'93'__20 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272
             (coe d_gtypeToPolyType_6 (coe v1)) (coe v2)
             (coe d_gtypeToPolyType_6 (coe v3))
      MAlonzo.Code.Once.Grammar.C__'8855'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'42'__268
             (coe d_gtypeToPolyType_6 (coe v1))
             (coe d_gtypeToPolyType_6 (coe v2))
      MAlonzo.Code.Once.Grammar.C__'8853'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'43'__270
             (coe d_gtypeToPolyType_6 (coe v1))
             (coe d_gtypeToPolyType_6 (coe v2))
      MAlonzo.Code.Once.Grammar.C_TEff_26 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C_PEff_274
             (coe d_gtypeToPolyType_6 (coe v1))
             (coe d_gtypeToPolyType_6 (coe v2))
      MAlonzo.Code.Once.Grammar.C_GMu_28 v1
        -> coe
             MAlonzo.Code.Once.Type.C_Pμ'45'type_276
             (coe d_gtypeToPolyFunctor_8 (coe v1))
      MAlonzo.Code.Once.Grammar.C_GNu_30 v1
        -> coe
             MAlonzo.Code.Once.Type.C_Pν'45'type_278
             (coe d_gtypeToPolyFunctor_8 (coe v1))
             (coe MAlonzo.Code.Once.Type.C_pure_34)
      MAlonzo.Code.Once.Grammar.C_GNuEff_32 v1
        -> coe
             MAlonzo.Code.Once.Type.C_Pν'45'type_278
             (coe d_gtypeToPolyFunctor_8 (coe v1))
             (coe MAlonzo.Code.Once.Type.C_eff_36)
      MAlonzo.Code.Once.Grammar.C_TVar_34 v1
        -> coe MAlonzo.Code.Once.Type.C_PTVar_284 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.gtypeToPolyFunctor
d_gtypeToPolyFunctor_8 ::
  MAlonzo.Code.Once.Grammar.T_GFunctor_10 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252
d_gtypeToPolyFunctor_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_GFK_36 v1
        -> coe
             MAlonzo.Code.Once.Type.C_PK_256 (coe d_gtypeToPolyType_6 (coe v1))
      MAlonzo.Code.Once.Grammar.C_GFId_38
        -> coe MAlonzo.Code.Once.Type.C_PId_258
      MAlonzo.Code.Once.Grammar.C_GFSum_40 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'8853'__260
             (coe d_gtypeToPolyFunctor_8 (coe v1))
             (coe d_gtypeToPolyFunctor_8 (coe v2))
      MAlonzo.Code.Once.Grammar.C_GFProd_42 v1 v2
        -> coe
             MAlonzo.Code.Once.Type.C__P'8855'__262
             (coe d_gtypeToPolyFunctor_8 (coe v1))
             (coe d_gtypeToPolyFunctor_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.wrapParams
d_wrapParams_46 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Grammar.T_GExpr_82 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_82
d_wrapParams_46 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Once.Grammar.C_ELam_94 (coe v2)
             (coe d_wrapParams_46 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.gdeclToDecl
d_gdeclToDecl_56 ::
  MAlonzo.Code.Once.Grammar.T_GDecl_114 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20
d_gdeclToDecl_56 v0
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
                     (coe d_wrapParams_46 (coe v2) (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                             (coe d_wrapParams_46 (coe v2) (coe v3)) (coe v5)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_DSignature_120 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_26 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe d_gtypeToPolyType_6 (coe v2)))
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
d_mapDecls_118 ::
  [MAlonzo.Code.Once.Grammar.T_GDecl_114] ->
  Maybe [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20]
d_mapDecls_118 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
      (:) v1 v2
        -> let v3 = d_gdeclToDecl_56 (coe v1) in
           coe
             (let v4 = d_mapDecls_118 (coe v2) in
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
d_gmoduleToModule_140 ::
  MAlonzo.Code.Once.Grammar.T_GModule_126 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_gmoduleToModule_140 v0
  = let v1
          = d_mapDecls_118
              (coe MAlonzo.Code.Once.Grammar.d_decls_130 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
