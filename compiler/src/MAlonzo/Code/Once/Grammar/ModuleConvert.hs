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
import qualified MAlonzo.Code.Data.Maybe.Base
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
-- Once.Grammar.ModuleConvert.gAllocToAlloc
d_gAllocToAlloc_42 ::
  MAlonzo.Code.Once.Grammar.T_AllocStrategy_112 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
d_gAllocToAlloc_42 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_Stack_114
        -> coe MAlonzo.Code.Once.Parser.Module.Core.C_Stack_10
      MAlonzo.Code.Once.Grammar.C_Arena_116
        -> coe MAlonzo.Code.Once.Parser.Module.Core.C_Arena_16
      MAlonzo.Code.Once.Grammar.C_Pool_118
        -> coe MAlonzo.Code.Once.Parser.Module.Core.C_Pool_14
      MAlonzo.Code.Once.Grammar.C_Heap_120
        -> coe MAlonzo.Code.Once.Parser.Module.Core.C_Heap_12
      MAlonzo.Code.Once.Grammar.C_Const_122
        -> coe MAlonzo.Code.Once.Parser.Module.Core.C_Const_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.wrapParams
d_wrapParams_44 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Grammar.T_GExpr_82 ->
  MAlonzo.Code.Once.Grammar.T_GExpr_82
d_wrapParams_44 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Once.Grammar.C_ELam_94 (coe v2)
             (coe d_wrapParams_44 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.gdeclToDecl
d_gdeclToDecl_54 ::
  MAlonzo.Code.Once.Grammar.T_GDecl_126 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32
d_gdeclToDecl_54 v0
  = case coe v0 of
      MAlonzo.Code.Once.Grammar.C_DTypeSig_128 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 (coe v1)
                (coe d_gtypeToPolyType_6 (coe v2)))
      MAlonzo.Code.Once.Grammar.C_DFunDef_130 v1 v2 v3 v4
        -> let v5
                 = MAlonzo.Code.Once.Grammar.ConcreteDec.d_concrete'63'_98
                     (coe d_wrapParams_44 (coe v2) (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 (coe v1)
                          (coe MAlonzo.Code.Data.Maybe.Base.du_map_64 d_gAllocToAlloc_42 v3)
                          (coe
                             MAlonzo.Code.Once.Grammar.ExprConvert.d_gexprToRaw_12
                             (coe d_wrapParams_44 (coe v2) (coe v4)) (coe v6)))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_DSignature_132 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                (coe d_gtypeToPolyType_6 (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      MAlonzo.Code.Once.Grammar.C_DTypeAlias_134 v1 v2 v3
        -> let v4
                 = MAlonzo.Code.Once.Grammar.Convert.d_gtypeToType_6 (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 (coe v1)
                          (coe v2) (coe v5))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Grammar.C_DImport_136 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42
                (coe
                   MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30 (coe v1)
                   (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Grammar.ModuleConvert.mapDecls
d_mapDecls_122 ::
  [MAlonzo.Code.Once.Grammar.T_GDecl_126] ->
  Maybe [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32]
d_mapDecls_122 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
      (:) v1 v2
        -> let v3 = d_gdeclToDecl_54 (coe v1) in
           coe
             (let v4 = d_mapDecls_122 (coe v2) in
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
d_gmoduleToModule_144 ::
  MAlonzo.Code.Once.Grammar.T_GModule_138 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_gmoduleToModule_144 v0
  = let v1
          = d_mapDecls_122
              (coe MAlonzo.Code.Once.Grammar.d_decls_142 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 (coe v2))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
