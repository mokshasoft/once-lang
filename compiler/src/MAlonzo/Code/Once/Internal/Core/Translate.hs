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

module MAlonzo.Code.Once.Internal.Core.Translate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Core.AbsTy
import qualified MAlonzo.Code.Once.Internal.Core.Abstract
import qualified MAlonzo.Code.Once.Internal.Core.PolySub
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Core.PolyTyping
import qualified MAlonzo.Code.Once.Internal.Core.Schema
import qualified MAlonzo.Code.Once.Internal.Core.Syntax
import qualified MAlonzo.Code.Once.Internal.Core.Telescope
import qualified MAlonzo.Code.Once.Internal.Core.Typing
import qualified MAlonzo.Code.Once.Internal.Elaboration
import qualified MAlonzo.Code.Once.Internal.Module
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Instance
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Internal.Core.Translate.monoSchema
d_monoSchema_8 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808
d_monoSchema_8 v0
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTy.C_schema_822
      (coe (0 :: Integer))
      (\ v1 ->
         coe MAlonzo.Code.Once.Internal.Core.Telescope.du_noKinds_96)
      (coe
         MAlonzo.Code.Once.Internal.Core.PolyTy.d_'8968'_'8969'_298
         (coe (0 :: Integer)) (coe v0))
-- Once.Internal.Core.Translate.ground-cf
d_ground'45'cf_16 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
d_ground'45'cf_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'Unit_72
        -> coe MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'Unit_386
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'Void_74
        -> coe MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'Void_388
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'Int_76
        -> coe MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'Int_390
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'Float_78
        -> coe MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'Float_392
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45''42'_84 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v7 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45''42'_398
                    (d_ground'45'cf_16 (coe v0) (coe v7) (coe v5))
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45''43'_90 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v7 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45''43'_404
                    (d_ground'45'cf_16 (coe v0) (coe v7) (coe v5))
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45''8658'_98 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45''8658'_412
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
                    (d_ground'45'cf_16 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'μ_102 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v5
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'μ_416
                    (d_groundF'45'cf_22 (coe v0) (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'ν_108 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v6 v7
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'ν_422
                    (d_groundF'45'cf_22 (coe v0) (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.groundF-cf
d_groundF'45'cf_22 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFreeF_70 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFreeF_378
d_groundF'45'cf_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'K_112 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C_K_12 v5
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'K_428
                    (d_ground'45'cf_16 (coe v0) (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45'Id_114
        -> coe MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45'Id_430
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45''8853'_120 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v7 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45''8853'_436
                    (d_groundF'45'cf_22 (coe v0) (coe v7) (coe v5))
                    (d_groundF'45'cf_22 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.WellFormed.C_rf'45''8855'_126 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v7 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Core.AbsTy.C_cf'45''8855'_442
                    (d_groundF'45'cf_22 (coe v0) (coe v7) (coe v5))
                    (d_groundF'45'cf_22 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.SigCF
d_SigCF_54 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 -> ()
d_SigCF_54 = erased
-- Once.Internal.Core.Translate.SigSig
d_SigSig_64 a0 a1 = ()
data T_SigSig_64
  = C_'91''93'_68 |
    C_s'45'ffi_76 AgdaAny
                  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68
                  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 T_SigSig_64
-- Once.Internal.Core.Translate.ImpSig
d_ImpSig_84 a0 a1 a2 a3 = ()
data T_ImpSig_84
  = C_'91''93'_92 |
    C_i'45'def_102 MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_ImpSig_84
-- Once.Internal.Core.Translate.TeleSig
d_TeleSig_110 a0 a1 a2 a3 = ()
data T_TeleSig_110
  = C_'91''93'_118 |
    C_t'45'def_126 MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_TeleSig_110
-- Once.Internal.Core.Translate.wkI
d_wkI_138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 -> T_ImpSig_84
d_wkI_138 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_wkI_138 v4 v5
du_wkI_138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 -> T_ImpSig_84
du_wkI_138 v0 v1
  = case coe v1 of
      C_'91''93'_92 -> coe v1
      C_i'45'def_102 v5 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C_i'45'def_102 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v5)
                    (coe du_wkI_138 (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.impDefs
d_impDefs_160 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 -> T_ImpSig_84
d_impDefs_160 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_impDefs_160 v3 v4 v5 v6 v7
du_impDefs_160 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 -> T_ImpSig_84
du_impDefs_160 v0 v1 v2 v3 v4
  = if coe v0
      then coe
             du_wkI_138
             (coe
                MAlonzo.Code.Once.Compile.d_extendDefs'45'at_680 (coe v0) (coe v3)
                (coe v1) (coe v2))
             (coe v4)
      else coe
             C_i'45'def_102 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             (coe du_wkI_138 (coe v3) (coe v4))
-- Once.Internal.Core.Translate.wkT
d_wkT_176 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 -> T_TeleSig_110
d_wkT_176 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_wkT_176 v4 v5
du_wkT_176 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 -> T_TeleSig_110
du_wkT_176 v0 v1
  = case coe v1 of
      C_'91''93'_118 -> coe v1
      C_t'45'def_126 v4 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    C_t'45'def_126 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4)
                    (coe du_wkT_176 (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate._.ES.Declared
d_Declared_196 a0 a1 a2 a3 a4 = ()
-- Once.Internal.Core.Translate._.ES.Elab
d_Elab_200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_Elab_200 = erased
-- Once.Internal.Core.Translate._.ES.ImportAt
d_ImportAt_202 a0 a1 a2 a3 a4 = ()
-- Once.Internal.Core.Translate._.ES.InstanceOf
d_InstanceOf_206 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_InstanceOf_206 = erased
-- Once.Internal.Core.Translate._.ES.View
d_View_208 a0 a1 a2 a3 a4 a5 = ()
-- Once.Internal.Core.Translate._.ES.Views
d_Views_212 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 -> ()
d_Views_212 = erased
-- Once.Internal.Core.Translate._.ES.appC
d_appC_214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appC_214 ~v0 ~v1 ~v2 = du_appC_214
du_appC_214 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appC_214 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.du_appC_700 v0 v2 v4 v5 v6
-- Once.Internal.Core.Translate._.ES.bin
d_bin_216 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin_216 ~v0 ~v1 ~v2 = du_bin_216
du_bin_216 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin_216 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Once.Internal.Elaboration.du_bin_708 v4 v5 v6
-- Once.Internal.Core.Translate._.ES.closeE
d_closeE_218 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closeE_218 ~v0 ~v1 ~v2 = du_closeE_218
du_closeE_218 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closeE_218 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Elaboration.du_closeE_776 v0 v2 v3
-- Once.Internal.Core.Translate._.ES.coerceE
d_coerceE_220 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coerceE_220 ~v0 ~v1 ~v2 = du_coerceE_220
du_coerceE_220 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coerceE_220 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.du_coerceE_726 v0 v1 v5
-- Once.Internal.Core.Translate._.ES.elabᵈ
d_elab'7496'_226 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_226 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_elab'7496'_818 (coe v0)
      (coe v1) (coe v2)
-- Once.Internal.Core.Translate._.ES.elabᵢ
d_elab'7522'_228 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_228 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_elab'7522'_804 (coe v0)
      (coe v1) (coe v2)
-- Once.Internal.Core.Translate._.ES.elabᶜ
d_elab'7580'_230 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_230 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_elab'7580'_794 (coe v0)
      (coe v1) (coe v2)
-- Once.Internal.Core.Translate._.ES.i2f
d_i2f_232 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_i2f_232 ~v0 ~v1 ~v2 = du_i2f_232
du_i2f_232 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_i2f_232 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Elaboration.du_i2f_724
-- Once.Internal.Core.Translate._.ES.importE
d_importE_234 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_importE_234 ~v0 ~v1 ~v2 = du_importE_234
du_importE_234 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_importE_234 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Elaboration.du_importE_770 v4
-- Once.Internal.Core.Translate._.ES.lift1
d_lift1_236 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift1_236 ~v0 ~v1 ~v2 = du_lift1_236
du_lift1_236 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift1_236 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe MAlonzo.Code.Once.Internal.Elaboration.du_lift1_664 v6 v7 v8
-- Once.Internal.Core.Translate._.ES.lift2
d_lift2_238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift2_238 ~v0 ~v1 ~v2 = du_lift2_238
du_lift2_238 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift2_238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.du_lift2_684 v8 v9 v10 v11
-- Once.Internal.Core.Translate._.ES.refE
d_refE_240 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refE_240 ~v0 ~v1 ~v2 = du_refE_240
du_refE_240 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refE_240 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Elaboration.du_refE_736 v3 v4
-- Once.Internal.Core.Translate._.ES.sigE
d_sigE_242 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigE_242 ~v0 ~v1 ~v2 = du_sigE_242
du_sigE_242 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigE_242 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.du_sigE_752 v0 v3 v4 v5 v6
-- Once.Internal.Core.Translate._.ES.subE
d_subE_244 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_subE_244 v9
du_subE_244 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_244 v0 = coe v0
-- Once.Internal.Core.Translate._.ES.Declared.honest
d_honest_248 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470 -> AgdaAny
d_honest_248 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_honest_482 (coe v0)
-- Once.Internal.Core.Translate._.ES.Declared.member
d_member_250 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_member_250 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_member_486 (coe v0)
-- Once.Internal.Core.Translate._.ES.Declared.rigid
d_rigid_252 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68
d_rigid_252 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_rigid_484 (coe v0)
-- Once.Internal.Core.Translate._.ES.ImportAt.entryOf
d_entryOf_256 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_256 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_entryOf_504 (coe v0)
-- Once.Internal.Core.Translate._.ES.ImportAt.instOf
d_instOf_258 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_258 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_instOf_506 (coe v0)
-- Once.Internal.Core.Translate._.ES.View.declares
d_declares_262 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470
d_declares_262 v0
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_declares_584 (coe v0)
-- Once.Internal.Core.Translate._.ES.View.entry
d_entry_264 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_264 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_entry_594 (coe v0)
-- Once.Internal.Core.Translate._.ES.View.ground
d_ground_266 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_266 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_ground_608 (coe v0)
-- Once.Internal.Core.Translate._.ES.View.imported
d_imported_268 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494
d_imported_268 v0
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_imported_578 (coe v0)
-- Once.Internal.Core.Translate._.ES.View.inst
d_inst_270 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_270 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_inst_622 (coe v0)
-- Once.Internal.Core.Translate._.mono-inst
d_mono'45'inst_276 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mono'45'inst_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_mono'45'inst_276
du_mono'45'inst_276 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mono'45'inst_276
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Once.Internal.Core.Translate._.poly-inst
d_poly'45'inst_294 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_poly'45'inst_294 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_poly'45'inst_294 v4 v7
du_poly'45'inst_294 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_poly'45'inst_294 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Core.Schema.du_kinded'45'instance_808
      (coe v0) (coe v1)
-- Once.Internal.Core.Translate._.impAt
d_impAt_316 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494
d_impAt_316 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_impAt_316 v3 v4 v5
du_impAt_316 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494
du_impAt_316 v0 v1 v2
  = case coe v1 of
      C_i'45'def_102 v6 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v13 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v11))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                      (coe v11) (coe v2)) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                -> if coe v14
                                     then coe
                                            seq (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Elaboration.C_def_508
                                               (coe v6) (coe du_mono'45'inst_276))
                                     else coe
                                            seq (coe v15)
                                            (coe du_impAt_316 (coe v10) (coe v8) (coe v2))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate._.sigAt
d_sigAt_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SigSig_64 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470
d_sigAt_396 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_sigAt_396 v3 v4 v5
du_sigAt_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SigSig_64 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470
du_sigAt_396 v0 v1 v2
  = case coe v1 of
      C_s'45'ffi_76 v6 v7 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> let v14
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v14 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v12))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                      (coe v12) (coe v2)) in
                         coe
                           (case coe v14 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                -> if coe v15
                                     then coe
                                            seq (coe v16)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Elaboration.C_declared_488
                                               (coe v6) (coe v7) (coe v8))
                                     else coe
                                            seq (coe v16)
                                            (coe du_sigAt_396 (coe v11) (coe v9) (coe v2))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate._.telFind
d_telFind_490 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_telFind_490 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_telFind_490 v3 v4 v5
du_telFind_490 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_telFind_490 v0 v1 v2
  = case coe v1 of
      C_t'45'def_126 v5 v7
        -> case coe v0 of
             (:) v8 v9
               -> let v10
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v10 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v8)))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                               (coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v8)) (coe v2)) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                         -> if coe v11
                              then coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased)
                              else coe
                                     seq (coe v12) (coe du_telFind_490 (coe v9) (coe v7) (coe v2))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate._.viewOf
d_viewOf_562 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 -> MAlonzo.Code.Once.Internal.Elaboration.T_View_516
d_viewOf_562 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_viewOf_562 v3 v4 v5 v6 v7 v8
du_viewOf_562 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 -> MAlonzo.Code.Once.Internal.Elaboration.T_View_516
du_viewOf_562 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.C_constructor_624
      (\ v6 v7 v8 -> coe du_impAt_316 (coe v1) (coe v4) v6)
      (\ v6 v7 v8 -> coe du_sigAt_396 (coe v0) (coe v3) v6)
      (coe
         (\ v6 v7 v8 v9 v10 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe du_telFind_490 (coe v2) (coe v5) (coe v6))))
      (coe
         (\ v6 v7 v8 v9 v10 v11 ->
            coe
              du_poly'45'inst_294 (coe v7)
              (coe MAlonzo.Code.Once.Type.Rigid.du_ground'45'kinded_350)))
      (coe
         (\ v6 v7 v8 v9 v10 v11 v12 -> coe du_poly'45'inst_294 (coe v7)))
-- Once.Internal.Core.Translate.u0
d_u0_608 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
d_u0_608 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 = du_u0_608 v5 v9
du_u0_608 ::
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
du_u0_608 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.Internal.Core.Translate.elabM
d_elabM_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Maybe MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elabM_628 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> coe
             MAlonzo.Code.Once.Internal.Elaboration.d_elab'7580'_794 (coe v0)
             (coe v1) (coe v2) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe v9)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Once.Internal.Elaboration.d_elab'7522'_804 (coe v0)
             (coe v1) (coe v2) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate._.monoElab
d_monoElab_660 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_monoElab_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      d_elabM_628 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v4))
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe MAlonzo.Code.Once.Internal.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_560
            (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
         (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3)))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)) (coe v5)
      (coe v6)
      (coe
         du_viewOf_562
         (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
         (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
         (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)) (coe v7)
         (coe v8) (coe v9))
      (coe v10)
-- Once.Internal.Core.Translate._.monoBody
d_monoBody_678 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
d_monoBody_678 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12
  = du_monoBody_678 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12
du_monoBody_678 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
du_monoBody_678 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_u0_608 (coe v6)
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_abs'45''8866'_934
         (coe (0 :: Integer))
         (\ v11 ->
            coe MAlonzo.Code.Once.Internal.Core.Telescope.du_noKinds_96)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_elabM_628 (coe v0) (coe v1) (coe v2)
               (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v4))
               (coe
                  MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Internal.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_560
                     (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
                  (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3)))
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)) (coe v5)
               (coe v6)
               (coe
                  du_viewOf_562
                  (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
                  (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                  (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)) (coe v7)
                  (coe v8) (coe v9))
               (coe v10)))
         (coe v5)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_monoElab_660 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))))
-- Once.Internal.Core.Translate.monoSg
d_monoSg_702 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
d_monoSg_702 ~v0 ~v1 v2 v3 v4 v5 v6 = du_monoSg_702 v2 v3 v4 v5 v6
du_monoSg_702 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
du_monoSg_702 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             d_ground'45'cf_16
             (coe
                MAlonzo.Code.Once.Internal.Core.PolyTy.d_arity_816
                (coe
                   MAlonzo.Code.Once.Internal.Core.PolyTy.du__'33''33'__848
                   (coe
                      MAlonzo.Code.Once.Internal.Core.PolyTy.C__'9655'__834 v0
                      (d_monoSchema_8 (coe v1)))
                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
             (coe v1) (coe v3)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 -> coe v2 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.polySg
d_polySg_722 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
d_polySg_722 ~v0 ~v1 ~v2 v3 v4 v5 = du_polySg_722 v3 v4 v5
du_polySg_722 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
du_polySg_722 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Once.Internal.Core.Schema.d_schemaOf'45'cf_796
             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v1))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v0 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate._.polyElab
d_polyElab_750 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_polyElab_750 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_elab'7580'_794 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe MAlonzo.Code.Once.Internal.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_560
            (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
         (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3)))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v4))
      (coe
         MAlonzo.Code.Once.Internal.Type.Instance.d_rigidOf_130
         (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
      (coe v5)
      (coe
         du_viewOf_562
         (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
         (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
         (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)) (coe v6)
         (coe v7) (coe v8))
      (coe v9)
-- Once.Internal.Core.Translate._.polyBody
d_polyBody_770 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
d_polyBody_770 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_polyBody_770 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_polyBody_770 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
du_polyBody_770 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_u0_608 (coe v5)
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_abs'45''8866'_934
         (coe
            MAlonzo.Code.Once.Internal.Type.Instance.d_arityOf_88
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Once.Internal.Core.Schema.d_kindsOf_352
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Internal.Elaboration.d_elab'7580'_794 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Internal.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_560
                     (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
                  (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3)))
               (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v4))
               (coe
                  MAlonzo.Code.Once.Internal.Type.Instance.d_rigidOf_130
                  (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
               (coe v5)
               (coe
                  du_viewOf_562
                  (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
                  (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                  (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)) (coe v6)
                  (coe v7) (coe v8))
               (coe v9)))
         (coe
            MAlonzo.Code.Once.Internal.Type.Instance.d_rigidOf_130
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_polyElab_750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))))
-- Once.Internal.Core.Translate.monoDef
d_monoDef_802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12
d_monoDef_802 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 v13
  = du_monoDef_802 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v13
du_monoDef_802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12
du_monoDef_802 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Internal.Core.Telescope.C_def_28 v7
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_absTm_694
         (coe
            MAlonzo.Code.Once.Internal.Core.PolyTy.d_arity_816
            (coe d_monoSchema_8 (coe v5)))
         (\ v12 ->
            coe MAlonzo.Code.Once.Internal.Core.Telescope.du_noKinds_96)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_monoElab_660 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v8) (coe v9) (coe v10) (coe v11))))
      (coe
         du_monoBody_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Internal.Core.Translate.polyDef
d_polyDef_846 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12
d_polyDef_846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11
  = du_polyDef_846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_polyDef_846 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12
du_polyDef_846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Internal.Core.Telescope.C_def_28 v6
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_absTm_694
         (coe
            MAlonzo.Code.Once.Internal.Core.PolyTy.d_arity_816
            (coe
               MAlonzo.Code.Once.Internal.Core.Schema.d_schemaOf_394
               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4))))
         (coe
            MAlonzo.Code.Once.Internal.Core.Schema.d_kindsOf_352
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_polyElab_750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v7) (coe v8) (coe v9) (coe v10))))
      (coe
         du_polyBody_770 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10))
-- Once.Internal.Core.Translate.programAt
d_programAt_876 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_MainEntry_98 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_programAt_876 ~v0 v1 v2 v3 v4 v5
  = du_programAt_876 v1 v2 v3 v4 v5
du_programAt_876 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_MainEntry_98 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
du_programAt_876 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Core.Telescope.C_program_130 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Internal.Core.Translate.⌈⌉-<:
d_'8968''8969''45''60''58'_890 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Core.PolySub.T__'60''58''8346'__10
d_'8968''8969''45''60''58'_890 ~v0 v1 v2 v3
  = du_'8968''8969''45''60''58'_890 v1 v2 v3
du_'8968''8969''45''60''58'_890 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Core.PolySub.T__'60''58''8346'__10
du_'8968''8969''45''60''58'_890 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'void_16
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'void_20
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'unit_22
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'int_24
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'float_26
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v10 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'arr_48
                           (coe du_'8968''8969''45''60''58'_890 (coe v16) (coe v13) (coe v10))
                           (coe du_'8968''8969''45''60''58'_890 (coe v15) (coe v18) (coe v11))
                           v12
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v11 v12
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'prod_58
                           (coe du_'8968''8969''45''60''58'_890 (coe v9) (coe v11) (coe v7))
                           (coe du_'8968''8969''45''60''58'_890 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v11 v12
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'sum_68
                           (coe du_'8968''8969''45''60''58'_890 (coe v9) (coe v11) (coe v7))
                           (coe du_'8968''8969''45''60''58'_890 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'μ_62
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'μ_72
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'ν_70 v6
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'ν_80 v6
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'rigid_76
        -> coe MAlonzo.Code.Once.Internal.Core.PolySub.C_sub'45'rigid_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.mainEntry
d_mainEntry_910 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_MainEntry_98
d_mainEntry_910 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Core.Telescope.C_entry_102
      (coe
         du_'8968''8969''45''60''58'_890 (coe v0)
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
            (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
               (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
            (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20))
         (coe v1))
-- Once.Internal.Core.Translate.SigIn
d_SigIn_922 ::
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 -> ()
d_SigIn_922 = erased
-- Once.Internal.Core.Translate.toProgram
d_toProgram_942 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_toProgram_942 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      MAlonzo.Code.Once.Internal.Module.C_ffi_84 v15 v19 v20 v21 v22
        -> case coe v4 of
             (:) v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v25
                      -> coe
                           d_toProgram_942 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Module.C_scope_20
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25))
                                    (coe v15))
                                 (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3)))
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
                           (coe v24) (coe v5)
                           (coe
                              C_s'45'ffi_76 v20 v21
                              (coe
                                 v12
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25))
                                    (coe v15))
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
                              v6)
                           (coe v7) (coe v8) (coe v9) (coe v22) (coe v11)
                           (coe
                              (\ v26 v27 ->
                                 coe
                                   v12 v26
                                   (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v27)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Module.C_mono_96 v15 v17 v21 v22 v23
        -> case coe v4 of
             (:) v24 v25
               -> case coe v24 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v26
                      -> coe
                           d_monoPick_968 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                           (coe v15) (coe v25) (coe v17) (coe v5) (coe v6) (coe v7) (coe v8)
                           (coe v9) (coe v21) (coe v22) (coe v23) (coe v11) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Module.C_poly_106 v16 v18 v19
        -> case coe v4 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v22
                      -> coe
                           d_toProgram_942 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Core.PolyTy.C__'9655'__834 v2
                              (MAlonzo.Code.Once.Internal.Core.Schema.d_schemaOf_394
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v22))))
                           (coe
                              MAlonzo.Code.Once.Internal.Module.C_scope_20
                              (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v22)
                                 (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))))
                           (coe v21)
                           (coe
                              du_polyDef_846 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                              (coe v16) (coe v5) (coe v6) (coe v7) (coe v8) (coe v18))
                           (coe v6)
                           (coe
                              du_wkI_138
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe v7))
                           (coe
                              C_t'45'def_126 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkT_176
                                 (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))
                                 (coe v8)))
                           (coe du_polySg_722 (coe v9) (coe v22)) (coe v19) (coe v11)
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.monoPick
d_monoPick_968 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_monoPick_968 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17
  = case coe v16 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
        -> case coe v18 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    du_monoHere_1046 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                    (coe v14) (coe v15) (coe v20) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
        -> coe
             d_monoDispatch_994 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v18)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
                (coe ("main" :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v5)
                (coe MAlonzo.Code.Once.Internal.Module.d_EffUU_168))
             (coe v17)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.monoDispatch
d_monoDispatch_994 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_monoDispatch_994 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18 v19
  = case coe v17 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
        -> if coe v20
             then coe
                    seq (coe v21)
                    (case coe v18 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                         -> if coe v22
                              then case coe v23 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                       -> coe
                                            du_monoHere_1046 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                            (coe v10) (coe v11) (coe v14) (coe v15) (coe v24)
                                            (coe v19)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v23)
                                     (coe
                                        d_monoNext_1020 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                                        (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
                                        (coe v19))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v21)
                    (coe
                       d_monoNext_1020 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v19))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.monoNext
d_monoNext_1020 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_monoNext_1020 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                v15 v16 v17
  = coe
      d_toProgram_942 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.Internal.Core.PolyTy.C__'9655'__834 v2
         (d_monoSchema_8 (coe v5)))
      (coe
         MAlonzo.Code.Once.Internal.Module.C_scope_20
         (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_extendDefs'45'at_680
            (coe
               MAlonzo.Code.Data.String.Properties.d__'61''61'__86
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
               (coe ("main" :: Data.Text.Text)))
            (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5))
         (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
      (coe v6)
      (coe
         du_monoDef_802 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v14))
      (coe v9)
      (coe
         du_impDefs_160
         (coe
            MAlonzo.Code.Data.String.Properties.d__'61''61'__86
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
            (coe ("main" :: Data.Text.Text)))
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5)
         (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
         (coe v10))
      (coe
         du_wkT_176
         (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))
         (coe v11))
      (coe du_monoSg_702 (coe v2) (coe v5) (coe v12) (coe v13)) (coe v15)
      (coe v16) (coe v17)
-- Once.Internal.Core.Translate.monoHere
d_monoHere_1046 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_monoHere_1046 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13 v14
                v15 v16 v17
  = du_monoHere_1046
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16 v17
du_monoHere_1046 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
du_monoHere_1046 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
                 v15
  = coe
      du_toProgramFrom_1062 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.Internal.Core.PolyTy.C__'9655'__834 v2
         (d_monoSchema_8 (coe v5)))
      (coe
         MAlonzo.Code.Once.Internal.Module.C_scope_20
         (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_extendDefs'45'at_680
            (coe
               MAlonzo.Code.Data.String.Properties.d__'61''61'__86
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
               (coe ("main" :: Data.Text.Text)))
            (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5))
         (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
      (coe v6)
      (coe
         du_monoDef_802 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12))
      (coe v9)
      (coe
         du_impDefs_160
         (coe
            MAlonzo.Code.Data.String.Properties.d__'61''61'__86
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
            (coe ("main" :: Data.Text.Text)))
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5)
         (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
         (coe v10))
      (coe
         du_wkT_176
         (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))
         (coe v11))
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
      (coe d_mainEntry_910 (coe v5) (coe v14)) (coe v13) (coe v15)
-- Once.Internal.Core.Translate.toProgramFrom
d_toProgramFrom_1062 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_MainEntry_98 ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_toProgramFrom_1062 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 v11 v12 v13
  = du_toProgramFrom_1062 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v11 v12 v13
du_toProgramFrom_1062 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_MainEntry_98 ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
du_toProgramFrom_1062 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v11 of
      MAlonzo.Code.Once.Internal.Module.C_'91''93'_74
        -> coe
             du_programAt_876 (coe v1) (coe v2) (coe v5) (coe v9) (coe v10)
      MAlonzo.Code.Once.Internal.Module.C_ffi_84 v15 v19 v20 v21 v22
        -> case coe v4 of
             (:) v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v25
                      -> coe
                           du_toProgramFrom_1062 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Internal.Module.C_scope_20
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25))
                                    (coe v15))
                                 (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3)))
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
                           (coe v24) (coe v5)
                           (coe
                              C_s'45'ffi_76 v20 v21
                              (coe
                                 v12
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25))
                                    (coe v15))
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
                              v6)
                           (coe v7) (coe v8) (coe v9) (coe v10) (coe v22)
                           (coe
                              (\ v26 v27 ->
                                 coe
                                   v12 v26
                                   (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v27)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Module.C_mono_96 v15 v17 v21 v22 v23
        -> case coe v4 of
             (:) v24 v25
               -> case coe v24 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v26
                      -> coe
                           du_toProgramFrom_1062 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Core.PolyTy.C__'9655'__834 v2
                              (d_monoSchema_8 (coe v15)))
                           (coe
                              MAlonzo.Code.Once.Internal.Module.C_scope_20
                              (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
                              (coe
                                 MAlonzo.Code.Once.Compile.d_extendDefs'45'at_680
                                 (coe
                                    MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v26))
                                    (coe ("main" :: Data.Text.Text)))
                                 (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v26)) (coe v15))
                              (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3)))
                           (coe v25)
                           (coe
                              du_monoDef_802 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                              (coe v15) (coe v17) (coe v5) (coe v6) (coe v7) (coe v8) (coe v22))
                           (coe v6)
                           (coe
                              du_impDefs_160
                              (coe
                                 MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v26))
                                 (coe ("main" :: Data.Text.Text)))
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v26)) (coe v15)
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe v7))
                           (coe
                              du_wkT_176
                              (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))
                              (coe v8))
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9) (coe v10) (coe v23)
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Module.C_poly_106 v16 v18 v19
        -> case coe v4 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v22
                      -> coe
                           du_toProgramFrom_1062 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Internal.Core.PolyTy.C__'9655'__834 v2
                              (MAlonzo.Code.Once.Internal.Core.Schema.d_schemaOf_394
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v22))))
                           (coe
                              MAlonzo.Code.Once.Internal.Module.C_scope_20
                              (coe MAlonzo.Code.Once.Internal.Module.d_sig_14 (coe v3))
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v22)
                                 (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))))
                           (coe v21)
                           (coe
                              du_polyDef_846 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                              (coe v16) (coe v5) (coe v6) (coe v7) (coe v8) (coe v18))
                           (coe v6)
                           (coe
                              du_wkI_138
                              (coe MAlonzo.Code.Once.Internal.Module.d_imps_16 (coe v3))
                              (coe v7))
                           (coe
                              C_t'45'def_126 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkT_176
                                 (coe MAlonzo.Code.Once.Internal.Module.d_tele_18 (coe v3))
                                 (coe v8)))
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9) (coe v10) (coe v19)
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.noCF
d_noCF_1488 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
d_noCF_1488 ~v0 ~v1 = du_noCF_1488
du_noCF_1488 ::
  MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374
du_noCF_1488 = MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Core.Translate.toProgram₀
d_toProgram'8320'_1494 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Internal.Module.T_ModTele_70 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Core.Telescope.T_Program_106
d_toProgram'8320'_1494 v0 v1 v2
  = coe
      d_toProgram_942
      (coe
         MAlonzo.Code.Once.Internal.Module.du_teleSig_136 (coe v0) (coe v1))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Internal.Core.PolyTy.C_'91''93'_830)
      (coe
         MAlonzo.Code.Once.Internal.Module.C_scope_20
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v0)
      (coe MAlonzo.Code.Once.Internal.Core.Telescope.C_'91''93'_16)
      (coe C_'91''93'_68) (coe C_'91''93'_92) (coe C_'91''93'_118)
      (\ v3 -> coe du_noCF_1488) (coe v1) (coe v2) (coe (\ v3 v4 -> v4))
