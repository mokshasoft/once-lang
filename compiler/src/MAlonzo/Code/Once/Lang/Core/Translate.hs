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

module MAlonzo.Code.Once.Lang.Core.Translate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.AbsTy
import qualified MAlonzo.Code.Once.Lang.Core.Abstract
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTyping
import qualified MAlonzo.Code.Once.Lang.Core.Schema
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.Telescope
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Elaboration
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Lang.Core.Translate.monoSchema
d_monoSchema_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808
d_monoSchema_8 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.C_schema_822
      (coe (0 :: Integer))
      (\ v1 -> coe MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
      (coe
         MAlonzo.Code.Once.Lang.Core.PolyTy.d_'8968'_'8969'_298
         (coe (0 :: Integer)) (coe v0))
-- Once.Lang.Core.Translate.ground-cf
d_ground'45'cf_16 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374
d_ground'45'cf_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Unit_72
        -> coe MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'Unit_386
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Void_74
        -> coe MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'Void_388
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Int_76
        -> coe MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'Int_390
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Float_78
        -> coe MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'Float_392
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''42'_84 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v7 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45''42'_398
                    (d_ground'45'cf_16 (coe v0) (coe v7) (coe v5))
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''43'_90 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v7 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45''43'_404
                    (d_ground'45'cf_16 (coe v0) (coe v7) (coe v5))
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45''8658'_412
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
                    (d_ground'45'cf_16 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'μ_102 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'μ_416
                    (d_groundF'45'cf_22 (coe v0) (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'ν_108 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'ν_422
                    (d_groundF'45'cf_22 (coe v0) (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.groundF-cf
d_groundF'45'cf_22 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFreeF_70 ->
  MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFreeF_378
d_groundF'45'cf_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'K_112 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'K_428
                    (d_ground'45'cf_16 (coe v0) (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Id_114
        -> coe MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45'Id_430
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8853'_120 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v7 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45''8853'_436
                    (d_groundF'45'cf_22 (coe v0) (coe v7) (coe v5))
                    (d_groundF'45'cf_22 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8855'_126 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v7 v8
               -> coe
                    MAlonzo.Code.Once.Lang.Core.AbsTy.C_cf'45''8855'_442
                    (d_groundF'45'cf_22 (coe v0) (coe v7) (coe v5))
                    (d_groundF'45'cf_22 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.SigCF
d_SigCF_54 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 -> ()
d_SigCF_54 = erased
-- Once.Lang.Core.Translate.SigSig
d_SigSig_64 a0 a1 = ()
data T_SigSig_64
  = C_'91''93'_68 |
    C_s'45'ffi_76 AgdaAny
                  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 T_SigSig_64
-- Once.Lang.Core.Translate.ImpSig
d_ImpSig_84 a0 a1 a2 a3 = ()
data T_ImpSig_84
  = C_'91''93'_92 |
    C_i'45'def_102 MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_ImpSig_84
-- Once.Lang.Core.Translate.TeleSig
d_TeleSig_110 a0 a1 a2 a3 = ()
data T_TeleSig_110
  = C_'91''93'_118 |
    C_t'45'def_126 MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_TeleSig_110
-- Once.Lang.Core.Translate.wkI
d_wkI_138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808 ->
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
-- Once.Lang.Core.Translate.wkT
d_wkT_156 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 -> T_TeleSig_110
d_wkT_156 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_wkT_156 v4 v5
du_wkT_156 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 -> T_TeleSig_110
du_wkT_156 v0 v1
  = case coe v1 of
      C_'91''93'_118 -> coe v1
      C_t'45'def_126 v4 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    C_t'45'def_126 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4)
                    (coe du_wkT_156 (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate._.ES.Declared
d_Declared_176 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.Translate._.ES.Elab
d_Elab_180 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_Elab_180 = erased
-- Once.Lang.Core.Translate._.ES.ImportAt
d_ImportAt_182 a0 a1 a2 a3 a4 = ()
-- Once.Lang.Core.Translate._.ES.InstanceOf
d_InstanceOf_186 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_InstanceOf_186 = erased
-- Once.Lang.Core.Translate._.ES.View
d_View_188 a0 a1 a2 a3 a4 a5 = ()
-- Once.Lang.Core.Translate._.ES.Views
d_Views_192 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 -> ()
d_Views_192 = erased
-- Once.Lang.Core.Translate._.ES.appC
d_appC_194 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appC_194 ~v0 ~v1 ~v2 = du_appC_194
du_appC_194 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appC_194 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_appC_700 v0 v2 v4 v5 v6
-- Once.Lang.Core.Translate._.ES.bin
d_bin_196 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin_196 ~v0 ~v1 ~v2 = du_bin_196
du_bin_196 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin_196 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_bin_708 v4 v5 v6
-- Once.Lang.Core.Translate._.ES.closeE
d_closeE_198 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closeE_198 ~v0 ~v1 ~v2 = du_closeE_198
du_closeE_198 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closeE_198 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_closeE_774 v0 v2 v3
-- Once.Lang.Core.Translate._.ES.coerceE
d_coerceE_200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coerceE_200 ~v0 ~v1 ~v2 = du_coerceE_200
du_coerceE_200 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coerceE_200 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_coerceE_726 v0 v1 v5
-- Once.Lang.Core.Translate._.ES.elabᵈ
d_elab'7496'_206 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_206 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7496'_816 (coe v0)
      (coe v1) (coe v2)
-- Once.Lang.Core.Translate._.ES.elabᵢ
d_elab'7522'_208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_208 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7522'_802 (coe v0)
      (coe v1) (coe v2)
-- Once.Lang.Core.Translate._.ES.elabᶜ
d_elab'7580'_210 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_210 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v0)
      (coe v1) (coe v2)
-- Once.Lang.Core.Translate._.ES.i2f
d_i2f_212 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_i2f_212 ~v0 ~v1 ~v2 = du_i2f_212
du_i2f_212 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_i2f_212 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_i2f_724
-- Once.Lang.Core.Translate._.ES.importE
d_importE_214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_importE_214 ~v0 ~v1 ~v2 = du_importE_214
du_importE_214 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_importE_214 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_importE_768 v4
-- Once.Lang.Core.Translate._.ES.lift1
d_lift1_216 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift1_216 ~v0 ~v1 ~v2 = du_lift1_216
du_lift1_216 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift1_216 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_lift1_664 v6 v7 v8
-- Once.Lang.Core.Translate._.ES.lift2
d_lift2_218 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift2_218 ~v0 ~v1 ~v2 = du_lift2_218
du_lift2_218 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift2_218 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_lift2_684 v8 v9 v10 v11
-- Once.Lang.Core.Translate._.ES.refE
d_refE_220 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refE_220 ~v0 ~v1 ~v2 = du_refE_220
du_refE_220 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refE_220 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_refE_736 v3 v4
-- Once.Lang.Core.Translate._.ES.sigE
d_sigE_222 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigE_222 ~v0 ~v1 ~v2 = du_sigE_222
du_sigE_222 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigE_222 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Lang.Elaboration.du_sigE_752 v0 v3 v4 v5
-- Once.Lang.Core.Translate._.ES.subE
d_subE_224 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_subE_224 v9
du_subE_224 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_224 v0 = coe v0
-- Once.Lang.Core.Translate._.ES.Declared.honest
d_honest_228 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470 -> AgdaAny
d_honest_228 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_honest_482 (coe v0)
-- Once.Lang.Core.Translate._.ES.Declared.member
d_member_230 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_member_230 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_member_486 (coe v0)
-- Once.Lang.Core.Translate._.ES.Declared.rigid
d_rigid_232 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_rigid_232 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_rigid_484 (coe v0)
-- Once.Lang.Core.Translate._.ES.ImportAt.entryOf
d_entryOf_236 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_236 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_entryOf_504 (coe v0)
-- Once.Lang.Core.Translate._.ES.ImportAt.instOf
d_instOf_238 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_238 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_instOf_506 (coe v0)
-- Once.Lang.Core.Translate._.ES.View.declares
d_declares_242 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470
d_declares_242 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_declares_584 (coe v0)
-- Once.Lang.Core.Translate._.ES.View.entry
d_entry_244 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_244 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_entry_594 (coe v0)
-- Once.Lang.Core.Translate._.ES.View.ground
d_ground_246 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_246 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_ground_608 (coe v0)
-- Once.Lang.Core.Translate._.ES.View.imported
d_imported_248 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494
d_imported_248 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_imported_578 (coe v0)
-- Once.Lang.Core.Translate._.ES.View.inst
d_inst_250 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_250 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_inst_622 (coe v0)
-- Once.Lang.Core.Translate._.mono-inst
d_mono'45'inst_256 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mono'45'inst_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_mono'45'inst_256
du_mono'45'inst_256 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mono'45'inst_256
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Once.Lang.Core.Translate._.poly-inst
d_poly'45'inst_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_poly'45'inst_274 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_poly'45'inst_274 v4 v7
du_poly'45'inst_274 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_poly'45'inst_274 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Schema.du_kinded'45'instance_808
      (coe v0) (coe v1)
-- Once.Lang.Core.Translate._.impAt
d_impAt_296 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494
d_impAt_296 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_impAt_296 v3 v4 v5
du_impAt_296 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_494
du_impAt_296 v0 v1 v2
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
                                               MAlonzo.Code.Once.Lang.Elaboration.C_def_508 (coe v6)
                                               (coe du_mono'45'inst_256))
                                     else coe
                                            seq (coe v15)
                                            (coe du_impAt_296 (coe v10) (coe v8) (coe v2))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate._.sigAt
d_sigAt_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SigSig_64 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470
d_sigAt_376 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_sigAt_376 v3 v4 v5
du_sigAt_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_SigSig_64 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_470
du_sigAt_376 v0 v1 v2
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
                                               MAlonzo.Code.Once.Lang.Elaboration.C_declared_488
                                               (coe v6) (coe v7) (coe v8))
                                     else coe
                                            seq (coe v16)
                                            (coe du_sigAt_376 (coe v11) (coe v9) (coe v2))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate._.telFind
d_telFind_470 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_telFind_470 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_telFind_470 v3 v4 v5
du_telFind_470 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_telFind_470 v0 v1 v2
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
                                     seq (coe v12) (coe du_telFind_470 (coe v9) (coe v7) (coe v2))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate._.viewOf
d_viewOf_542 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 -> MAlonzo.Code.Once.Lang.Elaboration.T_View_516
d_viewOf_542 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_viewOf_542 v3 v4 v5 v6 v7 v8
du_viewOf_542 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 -> MAlonzo.Code.Once.Lang.Elaboration.T_View_516
du_viewOf_542 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.C_constructor_624
      (\ v6 v7 v8 -> coe du_impAt_296 (coe v1) (coe v4) v6)
      (\ v6 v7 v8 -> coe du_sigAt_376 (coe v0) (coe v3) v6)
      (coe
         (\ v6 v7 v8 v9 v10 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe du_telFind_470 (coe v2) (coe v5) (coe v6))))
      (coe
         (\ v6 v7 v8 v9 v10 v11 ->
            coe
              du_poly'45'inst_274 (coe v7)
              (coe MAlonzo.Code.Once.Type.Rigid.du_ground'45'kinded_350)))
      (coe
         (\ v6 v7 v8 v9 v10 v11 v12 -> coe du_poly'45'inst_274 (coe v7)))
-- Once.Lang.Core.Translate.u0
d_u0_588 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_u0_588 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 = du_u0_588 v5 v9
du_u0_588 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_u0_588 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.Lang.Core.Translate._.monoElab
d_monoElab_610 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_monoElab_610 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
            (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
         (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3)))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)) (coe v5)
      (coe v6)
      (coe
         du_viewOf_542 (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
         (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
         (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)) (coe v7)
         (coe v8) (coe v9))
      (coe v10)
-- Once.Lang.Core.Translate._.monoBody
d_monoBody_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_monoBody_628 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12
  = du_monoBody_628 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12
du_monoBody_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_monoBody_628 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_u0_588 (coe v6)
      (coe
         MAlonzo.Code.Once.Lang.Core.Abstract.du_abs'45''8866'_984
         (coe (0 :: Integer))
         (\ v11 -> coe MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
                  (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3)))
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)) (coe v5)
               (coe v6)
               (coe
                  du_viewOf_542 (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
                  (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                  (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)) (coe v7)
                  (coe v8) (coe v9))
               (coe v10)))
         (coe v5)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_monoElab_610 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10))))
-- Once.Lang.Core.Translate.monoSg
d_monoSg_652 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374
d_monoSg_652 ~v0 ~v1 v2 v3 v4 v5 v6 = du_monoSg_652 v2 v3 v4 v5 v6
du_monoSg_652 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374
du_monoSg_652 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             d_ground'45'cf_16
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                (coe
                   MAlonzo.Code.Once.Lang.Core.PolyTy.du__'33''33'__848
                   (coe
                      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v0
                      (d_monoSchema_8 (coe v1)))
                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
             (coe v1) (coe v3)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 -> coe v2 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.polySg
d_polySg_672 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374
d_polySg_672 ~v0 ~v1 ~v2 v3 v4 v5 = du_polySg_672 v3 v4 v5
du_polySg_672 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374
du_polySg_672 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf'45'cf_796
             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v1))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v0 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate._.polyElab
d_polyElab_700 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_polyElab_700 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
            (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
         (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3)))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v4))
      (coe
         MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
         (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
      (coe v5)
      (coe
         du_viewOf_542 (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
         (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
         (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)) (coe v6)
         (coe v7) (coe v8))
      (coe v9)
-- Once.Lang.Core.Translate._.polyBody
d_polyBody_720 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
d_polyBody_720 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_polyBody_720 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_polyBody_720 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__774
du_polyBody_720 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_u0_588 (coe v5)
      (coe
         MAlonzo.Code.Once.Lang.Core.Abstract.du_abs'45''8866'_984
         (coe
            MAlonzo.Code.Once.Lang.Type.Instance.d_arityOf_88
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Once.Lang.Core.Schema.d_kindsOf_352
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_792 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                  (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_334
                     (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
                  (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3)))
               (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v4))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
                  (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
               (coe v5)
               (coe
                  du_viewOf_542 (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
                  (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                  (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)) (coe v6)
                  (coe v7) (coe v8))
               (coe v9)))
         (coe
            MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_polyElab_700 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))))
-- Once.Lang.Core.Translate.monoDef
d_monoDef_752 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
d_monoDef_752 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 v13
  = du_monoDef_752 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v13
du_monoDef_752 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
du_monoDef_752 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v7
      (coe
         MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
         (coe
            MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
            (coe d_monoSchema_8 (coe v5)))
         (\ v12 -> coe MAlonzo.Code.Once.Lang.Core.Telescope.du_noKinds_96)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_monoElab_610 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v8) (coe v9) (coe v10) (coe v11))))
      (coe
         du_monoBody_628 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v8) (coe v9) (coe v10) (coe v11))
-- Once.Lang.Core.Translate.polyDef
d_polyDef_796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
d_polyDef_796 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11
  = du_polyDef_796 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_polyDef_796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12
du_polyDef_796 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.C_def_28 v6
      (coe
         MAlonzo.Code.Once.Lang.Core.Abstract.du_absTm_744
         (coe
            MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
            (coe
               MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4))))
         (coe
            MAlonzo.Code.Once.Lang.Core.Schema.d_kindsOf_352
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_polyElab_700 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v7) (coe v8) (coe v9) (coe v10))))
      (coe
         du_polyBody_720 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10))
-- Once.Lang.Core.Translate.programAt
d_programAt_826 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_programAt_826 ~v0 v1 v2 v3 v4 ~v5 = du_programAt_826 v1 v2 v3 v4
du_programAt_826 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
du_programAt_826 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Telescope.C_program_124 v0 v1 v2 v3
-- Once.Lang.Core.Translate.SigIn
d_SigIn_842 ::
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 -> ()
d_SigIn_842 = erased
-- Once.Lang.Core.Translate.toProgram
d_toProgram_862 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_toProgram_862 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v15 v19 v20 v21 v22
        -> case coe v4 of
             (:) v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v25
                      -> coe
                           d_toProgram_862 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Lang.Module.C_scope_20
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25))
                                    (coe v15))
                                 (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3)))
                              (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                              (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
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
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v15 v16 v18 v23 v24 v25
        -> case coe v4 of
             (:) v26 v27
               -> case coe v26 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v28
                      -> coe
                           d_monoPick_888 (coe v0) (coe v1) (coe v2) (coe v3) (coe v28)
                           (coe v16) (coe v27) (coe v18) (coe v5) (coe v6) (coe v7) (coe v8)
                           (coe v9) (coe v23) (coe v24) (coe v25) (coe v11) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v16 v18 v19
        -> case coe v4 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v22
                      -> coe
                           d_toProgram_862 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v2
                              (MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v22))))
                           (coe
                              MAlonzo.Code.Once.Lang.Module.C_scope_20
                              (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
                              (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v22)
                                 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))))
                           (coe v21)
                           (coe
                              du_polyDef_796 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                              (coe v16) (coe v5) (coe v6) (coe v7) (coe v8) (coe v18))
                           (coe v6)
                           (coe
                              du_wkI_138 (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                              (coe v7))
                           (coe
                              C_t'45'def_126 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkT_156 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))
                                 (coe v8)))
                           (coe du_polySg_672 (coe v9) (coe v22)) (coe v19) (coe v11)
                           (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.monoPick
d_monoPick_888 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_monoPick_888 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17
  = case coe v16 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
        -> coe
             seq (coe v18)
             (coe
                du_monoHere_966 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                (coe v14) (coe v15) (coe v17))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
        -> coe
             d_monoDispatch_914 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v15) (coe v18)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
                (coe ("main" :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v5)
                (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150))
             (coe v17)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.monoDispatch
d_monoDispatch_914 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_monoDispatch_914 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18 v19
  = case coe v17 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
        -> if coe v20
             then coe
                    seq (coe v21)
                    (case coe v18 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                         -> if coe v22
                              then coe
                                     seq (coe v23)
                                     (coe
                                        du_monoHere_966 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                                        (coe v11) (coe v14) (coe v15) (coe v19))
                              else coe
                                     seq (coe v23)
                                     (coe
                                        d_monoNext_940 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                                        (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v16)
                                        (coe v19))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v21)
                    (coe
                       d_monoNext_940 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v12) (coe v13) (coe v14) (coe v15) (coe v16) (coe v19))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.monoNext
d_monoNext_940 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_monoNext_940 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16 v17
  = coe
      d_toProgram_862 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v2
         (d_monoSchema_8 (coe v5)))
      (coe
         MAlonzo.Code.Once.Lang.Module.C_scope_20
         (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5))
            (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3)))
         (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
      (coe v6)
      (coe
         du_monoDef_752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v14))
      (coe v9)
      (coe
         C_i'45'def_102 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
         (coe
            du_wkI_138 (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
            (coe v10)))
      (coe
         du_wkT_156 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))
         (coe v11))
      (coe du_monoSg_652 (coe v2) (coe v5) (coe v12) (coe v13)) (coe v15)
      (coe v16) (coe v17)
-- Once.Lang.Core.Translate.monoHere
d_monoHere_966 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_monoHere_966 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 ~v13 v14
               v15 ~v16 v17
  = du_monoHere_966 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v17
du_monoHere_966 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
du_monoHere_966 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      du_toProgramFrom_982 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v2
         (d_monoSchema_8 (coe v5)))
      (coe
         MAlonzo.Code.Once.Lang.Module.C_scope_20
         (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5))
            (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3)))
         (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
      (coe v6)
      (coe
         du_monoDef_752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11) (coe v12))
      (coe v9)
      (coe
         C_i'45'def_102 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
         (coe
            du_wkI_138 (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
            (coe v10)))
      (coe
         du_wkT_156 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))
         (coe v11))
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v13) (coe v14)
-- Once.Lang.Core.Translate.toProgramFrom
d_toProgramFrom_982 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_toProgramFrom_982 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 ~v11 v12 v13
  = du_toProgramFrom_982 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v12 v13
du_toProgramFrom_982 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Tele_12 ->
  T_SigSig_64 ->
  T_ImpSig_84 ->
  T_TeleSig_110 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
du_toProgramFrom_982 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_54
        -> coe du_programAt_826 (coe v1) (coe v2) (coe v5) (coe v9)
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v14 v18 v19 v20 v21
        -> case coe v4 of
             (:) v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v24
                      -> coe
                           du_toProgramFrom_982 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Lang.Module.C_scope_20
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v24))
                                    (coe v14))
                                 (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3)))
                              (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                              (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
                           (coe v23) (coe v5)
                           (coe
                              C_s'45'ffi_76 v19 v20
                              (coe
                                 v11
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v24))
                                    (coe v14))
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
                              v6)
                           (coe v7) (coe v8) (coe v9) (coe v21)
                           (coe
                              (\ v25 v26 ->
                                 coe
                                   v11 v25
                                   (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v26)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v14 v15 v17 v22 v23 v24
        -> case coe v4 of
             (:) v25 v26
               -> case coe v25 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v27
                      -> coe
                           du_toProgramFrom_982 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v2
                              (d_monoSchema_8 (coe v15)))
                           (coe
                              MAlonzo.Code.Once.Lang.Module.C_scope_20
                              (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v27))
                                    (coe v15))
                                 (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3)))
                              (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3)))
                           (coe v26)
                           (coe
                              du_monoDef_752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v27)
                              (coe v15) (coe v17) (coe v5) (coe v6) (coe v7) (coe v8) (coe v23))
                           (coe v6)
                           (coe
                              C_i'45'def_102 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkI_138 (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                                 (coe v7)))
                           (coe
                              du_wkT_156 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))
                              (coe v8))
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9) (coe v24) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v15 v17 v18
        -> case coe v4 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v21
                      -> coe
                           du_toProgramFrom_982 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v2
                              (MAlonzo.Code.Once.Lang.Core.Schema.d_schemaOf_394
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v21))))
                           (coe
                              MAlonzo.Code.Once.Lang.Module.C_scope_20
                              (coe MAlonzo.Code.Once.Lang.Module.d_sig_14 (coe v3))
                              (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v21)
                                 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))))
                           (coe v20)
                           (coe
                              du_polyDef_796 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                              (coe v15) (coe v5) (coe v6) (coe v7) (coe v8) (coe v17))
                           (coe v6)
                           (coe
                              du_wkI_138 (coe MAlonzo.Code.Once.Lang.Module.d_imps_16 (coe v3))
                              (coe v7))
                           (coe
                              C_t'45'def_126 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkT_156 (coe MAlonzo.Code.Once.Lang.Module.d_tele_18 (coe v3))
                                 (coe v8)))
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9) (coe v18) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Translate.toProgram₀
d_toProgram'8320'_1414 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_100
d_toProgram'8320'_1414 v0 v1 v2
  = coe
      d_toProgram_862
      (coe
         MAlonzo.Code.Once.Lang.Module.du_teleSig_118 (coe v0) (coe v1))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_'91''93'_830)
      (coe
         MAlonzo.Code.Once.Lang.Module.C_scope_20
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v0) (coe MAlonzo.Code.Once.Lang.Core.Telescope.C_'91''93'_16)
      (coe C_'91''93'_68) (coe C_'91''93'_92) (coe C_'91''93'_118) erased
      (coe v1) (coe v2) (coe (\ v3 v4 -> v4))
