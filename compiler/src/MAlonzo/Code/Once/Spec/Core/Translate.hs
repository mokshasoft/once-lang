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

module MAlonzo.Code.Once.Spec.Core.Translate where

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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.Abstract
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Schema
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Telescope
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Spec.Core.Translate.monoSchema
d_monoSchema_8 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846
d_monoSchema_8 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_schema_860
      (coe (0 :: Integer))
      (\ v1 -> coe MAlonzo.Code.Once.Spec.Core.Telescope.du_noKinds_96)
      (coe
         MAlonzo.Code.Once.Spec.Core.PolyTy.d_'8968'_'8969'_336
         (coe (0 :: Integer)) (coe v0))
-- Once.Spec.Core.Translate.ground-cf
d_ground'45'cf_16 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
d_ground'45'cf_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'Unit_752
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Unit_386
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'Void_754
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Void_388
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'Int_756
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Int_390
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'Float_758
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Float_392
      MAlonzo.Code.Once.Type.Rigid.C_rf'45''42'_764 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''42'_398
                    (d_ground'45'cf_16 (coe v0) (coe v7) (coe v5))
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Rigid.C_rf'45''43'_770 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''43'_404
                    (d_ground'45'cf_16 (coe v0) (coe v7) (coe v5))
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Rigid.C_rf'45''8658'_778 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8658'_412
                    (d_ground'45'cf_16 (coe v0) (coe v8) (coe v6))
                    (d_ground'45'cf_16 (coe v0) (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'μ_782 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_μ'45'type_130 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'μ_416
                    (d_groundF'45'cf_22 (coe v0) (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'ν_788 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_132 v6 v7
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'ν_422
                    (d_groundF'45'cf_22 (coe v0) (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.groundF-cf
d_groundF'45'cf_22 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFreeF_750 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFreeF_378
d_groundF'45'cf_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'K_792 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'K_428
                    (d_ground'45'cf_16 (coe v0) (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Rigid.C_rf'45'Id_794
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Id_430
      MAlonzo.Code.Once.Type.Rigid.C_rf'45''8853'_800 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8853'_436
                    (d_groundF'45'cf_22 (coe v0) (coe v7) (coe v5))
                    (d_groundF'45'cf_22 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.Rigid.C_rf'45''8855'_806 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
               -> coe
                    MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8855'_442
                    (d_groundF'45'cf_22 (coe v0) (coe v7) (coe v5))
                    (d_groundF'45'cf_22 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.SigCF
d_SigCF_54 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 -> ()
d_SigCF_54 = erased
-- Once.Spec.Core.Translate.ImpSig
d_ImpSig_68 a0 a1 a2 a3 = ()
data T_ImpSig_68
  = C_'91''93'_76 |
    C_i'45'ffi_84 MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222
                  AgdaAny MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 T_ImpSig_68 |
    C_i'45'def_94 MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_ImpSig_68
-- Once.Spec.Core.Translate.TeleSig
d_TeleSig_102 a0 a1 a2 a3 = ()
data T_TeleSig_102
  = C_'91''93'_110 |
    C_t'45'def_118 MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_TeleSig_102
-- Once.Spec.Core.Translate.wkI
d_wkI_130 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_68 -> T_ImpSig_68
d_wkI_130 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_wkI_130 v4 v5
du_wkI_130 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_68 -> T_ImpSig_68
du_wkI_130 v0 v1
  = case coe v1 of
      C_'91''93'_76 -> coe v1
      C_i'45'ffi_84 v5 v6 v7 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> coe
                    C_i'45'ffi_84 v5 v6 v7 v8 (coe du_wkI_130 (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'def_94 v5 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    C_i'45'def_94 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v5)
                    (coe du_wkI_130 (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.wkT
d_wkT_158 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_102 -> T_TeleSig_102
d_wkT_158 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_wkT_158 v4 v5
du_wkT_158 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_102 -> T_TeleSig_102
du_wkT_158 v0 v1
  = case coe v1 of
      C_'91''93'_110 -> coe v1
      C_t'45'def_118 v4 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    C_t'45'def_118 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4)
                    (coe du_wkT_158 (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate._.ES.Elab
d_Elab_178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_Elab_178 = erased
-- Once.Spec.Core.Translate._.ES.ImportAt
d_ImportAt_180 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.Translate._.ES.InstanceOf
d_InstanceOf_182 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_InstanceOf_182 = erased
-- Once.Spec.Core.Translate._.ES.View
d_View_184 a0 a1 a2 a3 a4 = ()
-- Once.Spec.Core.Translate._.ES.Views
d_Views_188 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 -> ()
d_Views_188 = erased
-- Once.Spec.Core.Translate._.ES.appC
d_appC_190 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appC_190 ~v0 ~v1 ~v2 = du_appC_190
du_appC_190 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appC_190 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_appC_638 v0 v2 v4 v5 v6
-- Once.Spec.Core.Translate._.ES.bin
d_bin_192 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin_192 ~v0 ~v1 ~v2 = du_bin_192
du_bin_192 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin_192 v0 v1 v2 v3 v4 v5 v6 v7
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_bin_646 v4 v5 v6
-- Once.Spec.Core.Translate._.ES.closeE
d_closeE_194 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closeE_194 ~v0 ~v1 ~v2 = du_closeE_194
du_closeE_194 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closeE_194 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_closeE_712 v0 v2 v3
-- Once.Spec.Core.Translate._.ES.coerceE
d_coerceE_196 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coerceE_196 ~v0 ~v1 ~v2 = du_coerceE_196
du_coerceE_196 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coerceE_196 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_coerceE_664 v0 v1 v5
-- Once.Spec.Core.Translate._.ES.elabᵈ
d_elab'7496'_200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_200 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7496'_754 (coe v0)
      (coe v1) (coe v2)
-- Once.Spec.Core.Translate._.ES.elabᵢ
d_elab'7522'_202 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_202 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7522'_740 (coe v0)
      (coe v1) (coe v2)
-- Once.Spec.Core.Translate._.ES.elabᶜ
d_elab'7580'_204 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_204 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_730 (coe v0)
      (coe v1) (coe v2)
-- Once.Spec.Core.Translate._.ES.i2f
d_i2f_208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_i2f_208 ~v0 ~v1 ~v2 = du_i2f_208
du_i2f_208 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_i2f_208 v0 v1 v2
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_i2f_662
-- Once.Spec.Core.Translate._.ES.importE
d_importE_210 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_importE_210 ~v0 ~v1 ~v2 = du_importE_210
du_importE_210 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_importE_210 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_importE_690 v0 v3 v4 v5
-- Once.Spec.Core.Translate._.ES.lift1
d_lift1_212 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift1_212 ~v0 ~v1 ~v2 = du_lift1_212
du_lift1_212 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift1_212 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_lift1_602 v6 v7 v8
-- Once.Spec.Core.Translate._.ES.lift2
d_lift2_214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift2_214 ~v0 ~v1 ~v2 = du_lift2_214
du_lift2_214 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift2_214 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_lift2_622 v8 v9 v10 v11
-- Once.Spec.Core.Translate._.ES.refE
d_refE_216 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refE_216 ~v0 ~v1 ~v2 = du_refE_216
du_refE_216 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refE_216 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_refE_674 v3 v4
-- Once.Spec.Core.Translate._.ES.subE
d_subE_218 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_subE_218 v9
du_subE_218 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_218 v0 = coe v0
-- Once.Spec.Core.Translate._.ES.View.entry
d_entry_228 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_228 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entry_532 (coe v0)
-- Once.Spec.Core.Translate._.ES.View.ground
d_ground_230 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_230 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_ground_546 (coe v0)
-- Once.Spec.Core.Translate._.ES.View.imported
d_imported_232 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452
d_imported_232 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_imported_522 (coe v0)
-- Once.Spec.Core.Translate._.ES.View.inst
d_inst_234 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_234 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_inst_560 (coe v0)
-- Once.Spec.Core.Translate._.mono-inst
d_mono'45'inst_240 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mono'45'inst_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_mono'45'inst_240
du_mono'45'inst_240 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mono'45'inst_240
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Once.Spec.Core.Translate._.poly-inst
d_poly'45'inst_258 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_poly'45'inst_258 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_poly'45'inst_258 v4 v7
du_poly'45'inst_258 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_poly'45'inst_258 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Schema.du_kinded'45'instance_778
      (coe v0) (coe v1)
-- Once.Spec.Core.Translate._.impAt
d_impAt_280 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452
d_impAt_280 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 = du_impAt_280 v3 v4 v5
du_impAt_280 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_ImpSig_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452
du_impAt_280 v0 v1 v2
  = case coe v1 of
      C_i'45'ffi_84 v6 v7 v8 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> let v15
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v15 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v13))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                      (coe v13) (coe v2)) in
                         coe
                           (case coe v15 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                -> if coe v16
                                     then coe
                                            seq (coe v17)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Elaboration.C_ffi_458 (coe v7)
                                               (coe v8) (coe v9))
                                     else coe
                                            seq (coe v17)
                                            (coe du_impAt_280 (coe v12) (coe v10) (coe v2))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'def_94 v6 v8
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
                                               MAlonzo.Code.Once.Spec.Elaboration.C_def_462 (coe v6)
                                               (coe du_mono'45'inst_240))
                                     else coe
                                            seq (coe v15)
                                            (coe du_impAt_280 (coe v10) (coe v8) (coe v2))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate._.telFind
d_telFind_454 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_102 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_telFind_454 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_telFind_454 v3 v4 v5
du_telFind_454 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_TeleSig_102 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_telFind_454 v0 v1 v2
  = case coe v1 of
      C_t'45'def_118 v5 v7
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
                                     seq (coe v12) (coe du_telFind_454 (coe v9) (coe v7) (coe v2))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate._.viewOf
d_viewOf_524 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_ImpSig_68 ->
  T_TeleSig_102 -> MAlonzo.Code.Once.Spec.Elaboration.T_View_468
d_viewOf_524 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_viewOf_524 v3 v4 v5 v6
du_viewOf_524 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  T_ImpSig_68 ->
  T_TeleSig_102 -> MAlonzo.Code.Once.Spec.Elaboration.T_View_468
du_viewOf_524 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.C_constructor_562
      (\ v4 v5 v6 -> coe du_impAt_280 (coe v0) (coe v2) v4)
      (coe
         (\ v4 v5 v6 v7 v8 ->
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe du_telFind_454 (coe v1) (coe v3) (coe v4))))
      (coe
         (\ v4 v5 v6 v7 v8 v9 ->
            coe
              du_poly'45'inst_258 (coe v5)
              (coe MAlonzo.Code.Once.Type.Rigid.du_ground'45'kinded_458)))
      (coe (\ v4 v5 v6 v7 v8 v9 v10 -> coe du_poly'45'inst_258 (coe v5)))
-- Once.Spec.Core.Translate.u0
d_u0_568 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_382 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
d_u0_568 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 = du_u0_568 v5 v9
du_u0_568 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
du_u0_568 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.Spec.Core.Translate._.monoElab
d_monoElab_590 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_monoElab_590 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_730 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_272
            (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))))
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)) (coe v5)
      (coe v6)
      (coe
         du_viewOf_524
         (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
         (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)) (coe v7)
         (coe v8))
      (coe v9)
-- Once.Spec.Core.Translate._.monoBody
d_monoBody_604 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
d_monoBody_604 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10 v11
  = du_monoBody_604 v0 v1 v2 v3 v4 v5 v6 v7 v8 v11
du_monoBody_604 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
du_monoBody_604 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      du_u0_568 (coe v6)
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_abs'45''8866'_924
         (coe (0 :: Integer))
         (\ v10 -> coe MAlonzo.Code.Once.Spec.Core.Telescope.du_noKinds_96)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_730 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_272
                     (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))))
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)) (coe v5)
               (coe v6)
               (coe
                  du_viewOf_524
                  (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                  (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)) (coe v7)
                  (coe v8))
               (coe v9)))
         (coe v5) (coe MAlonzo.Code.Once.Type.C_pure_34)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_monoElab_590 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))))
-- Once.Spec.Core.Translate.monoSg
d_monoSg_626 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
d_monoSg_626 ~v0 ~v1 v2 v3 v4 v5 v6 = du_monoSg_626 v2 v3 v4 v5 v6
du_monoSg_626 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
du_monoSg_626 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             d_ground'45'cf_16
             (coe
                MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
                (coe
                   MAlonzo.Code.Once.Spec.Core.PolyTy.du__'33''33'__886
                   (coe
                      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v0
                      (d_monoSchema_8 (coe v1)))
                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
             (coe v1) (coe v3)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 -> coe v2 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.polySg
d_polySg_646 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
d_polySg_646 ~v0 ~v1 ~v2 v3 v4 v5 = du_polySg_646 v3 v4 v5
du_polySg_646 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
du_polySg_646 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf'45'cf_766
             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v1))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v0 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate._.polyElab
d_polyElab_674 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_polyElab_674 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_730 (coe v0)
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
         (coe
            MAlonzo.Code.Once.Compile.d_buildPolyCtx_272
            (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v4))
      (coe
         MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
         (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
      (coe v5)
      (coe
         du_viewOf_524
         (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
         (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)) (coe v6)
         (coe v7))
      (coe v8)
-- Once.Spec.Core.Translate._.polyBody
d_polyBody_690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
d_polyBody_690 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_polyBody_690 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_polyBody_690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__722
du_polyBody_690 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      du_u0_568 (coe v5)
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_abs'45''8866'_924
         (coe
            MAlonzo.Code.Once.Type.Rigid.d_arityOf_82
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Schema.d_kindsOf_352
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_730 (coe v0)
               (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                  (coe
                     MAlonzo.Code.Once.Compile.d_buildPolyCtx_272
                     (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))))
               (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v4))
               (coe
                  MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
                  (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
               (coe v5)
               (coe
                  du_viewOf_524
                  (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                  (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)) (coe v6)
                  (coe v7))
               (coe v8)))
         (coe
            MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe MAlonzo.Code.Once.Type.C_pure_34)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_polyElab_674 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v7) (coe v8))))
-- Once.Spec.Core.Translate.monoDef
d_monoDef_718 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
d_monoDef_718 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 v12
  = du_monoDef_718 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v12
du_monoDef_718 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
du_monoDef_718 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.C_def_28 v7
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_absTm_714
         (coe
            MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
            (coe d_monoSchema_8 (coe v5)))
         (\ v11 -> coe MAlonzo.Code.Once.Spec.Core.Telescope.du_noKinds_96)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_monoElab_590 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v6) (coe v8) (coe v9) (coe v10))))
      (coe
         du_monoBody_604 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v8) (coe v9) (coe v10))
-- Once.Spec.Core.Translate.polyDef
d_polyDef_758 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
d_polyDef_758 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_polyDef_758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_polyDef_758 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12
du_polyDef_758 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.C_def_28 v6
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_absTm_714
         (coe
            MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
            (coe
               MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf_394
               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4))))
         (coe
            MAlonzo.Code.Once.Spec.Core.Schema.d_kindsOf_352
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v4)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               d_polyElab_674 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v7) (coe v8) (coe v9))))
      (coe
         du_polyBody_690 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9))
-- Once.Spec.Core.Translate.programAt
d_programAt_786 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_programAt_786 ~v0 v1 v2 v3 v4 ~v5 = du_programAt_786 v1 v2 v3 v4
du_programAt_786 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
du_programAt_786 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.Telescope.C_program_124 v0 v1 v2 v3
-- Once.Spec.Core.Translate.SigIn
d_SigIn_802 ::
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 -> ()
d_SigIn_802 = erased
-- Once.Spec.Core.Translate.toProgram
d_toProgram_822 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_toProgram_822 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      MAlonzo.Code.Once.Spec.Module.C_ffi_52 v14 v18 v19 v20 v21
        -> case coe v4 of
             (:) v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v24
                      -> coe
                           d_toProgram_822 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Spec.Module.C_scope_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v24))
                                    (coe v14))
                                 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3)))
                              (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)))
                           (coe v23) (coe v5)
                           (coe
                              C_i'45'ffi_84 v18 v19 v20
                              (coe
                                 v11
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v24))
                                    (coe v14))
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
                              v6)
                           (coe v7) (coe v8) (coe v21) (coe v10)
                           (coe
                              (\ v25 v26 ->
                                 coe
                                   v11 v25
                                   (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v26)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_mono_64 v14 v16 v19 v20 v21
        -> case coe v4 of
             (:) v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v24
                      -> coe
                           d_monoPick_846 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                           (coe v14) (coe v23) (coe v16) (coe v5) (coe v6) (coe v7) (coe v8)
                           (coe v19) (coe v20) (coe v21) (coe v10) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_poly_74 v15 v16 v17
        -> case coe v4 of
             (:) v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v20
                      -> coe
                           d_toProgram_822 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v2
                              (MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf_394
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v20))))
                           (coe
                              MAlonzo.Code.Once.Spec.Module.C_scope_16
                              (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v20)
                                 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))))
                           (coe v19)
                           (coe
                              du_polyDef_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe v15) (coe v5) (coe v6) (coe v7) (coe v16))
                           (coe
                              du_wkI_130 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                              (coe v6))
                           (coe
                              C_t'45'def_118 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkT_158 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))
                                 (coe v7)))
                           (coe du_polySg_646 (coe v8) (coe v20)) (coe v17) (coe v10)
                           (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.monoPick
d_monoPick_846 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_monoPick_846 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16
  = case coe v15 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
        -> coe
             seq (coe v17)
             (coe
                du_monoHere_918 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v13)
                (coe v14) (coe v16))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
        -> coe
             d_monoDispatch_870 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
             (coe v12) (coe v13) (coe v14) (coe v17)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4))
                (coe ("main" :: Data.Text.Text)))
             (coe
                MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v5)
                (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_176))
             (coe v16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.monoDispatch
d_monoDispatch_870 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_monoDispatch_870 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                   v14 v15 v16 v17 v18
  = case coe v16 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
        -> if coe v19
             then coe
                    seq (coe v20)
                    (case coe v17 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                         -> if coe v21
                              then coe
                                     seq (coe v22)
                                     (coe
                                        du_monoHere_918 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                                        (coe v13) (coe v14) (coe v18))
                              else coe
                                     seq (coe v22)
                                     (coe
                                        d_monoNext_894 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
                                        (coe v11) (coe v12) (coe v13) (coe v14) (coe v15) (coe v18))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v20)
                    (coe
                       d_monoNext_894 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11)
                       (coe v12) (coe v13) (coe v14) (coe v15) (coe v18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.monoNext
d_monoNext_894 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_monoNext_894 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
               v15 v16
  = coe
      d_toProgram_822 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v2
         (d_monoSchema_8 (coe v5)))
      (coe
         MAlonzo.Code.Once.Spec.Module.C_scope_16
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5))
            (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3)))
         (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)))
      (coe v6)
      (coe
         du_monoDef_718 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10) (coe v13))
      (coe
         C_i'45'def_94 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
         (coe
            du_wkI_130 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
            (coe v9)))
      (coe
         du_wkT_158 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))
         (coe v10))
      (coe du_monoSg_626 (coe v2) (coe v5) (coe v11) (coe v12)) (coe v14)
      (coe v15) (coe v16)
-- Once.Spec.Core.Translate.monoHere
d_monoHere_918 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_monoHere_918 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 ~v12 v13 v14
               ~v15 v16
  = du_monoHere_918 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v13 v14 v16
du_monoHere_918 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
du_monoHere_918 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = coe
      du_toProgramFrom_934 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v2
         (d_monoSchema_8 (coe v5)))
      (coe
         MAlonzo.Code.Once.Spec.Module.C_scope_16
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v5))
            (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3)))
         (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)))
      (coe v6)
      (coe
         du_monoDef_718 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7) (coe v8) (coe v9) (coe v10) (coe v11))
      (coe
         C_i'45'def_94 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
         (coe
            du_wkI_130 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
            (coe v9)))
      (coe
         du_wkT_158 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))
         (coe v10))
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v12) (coe v13)
-- Once.Spec.Core.Translate.toProgramFrom
d_toProgramFrom_934 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_toProgramFrom_934 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 ~v10 v11 v12
  = du_toProgramFrom_934 v0 v1 v2 v3 v4 v5 v6 v7 v9 v11 v12
du_toProgramFrom_934 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Tele_12 ->
  T_ImpSig_68 ->
  T_TeleSig_102 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
du_toProgramFrom_934 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Once.Spec.Module.C_'91''93'_42
        -> coe du_programAt_786 (coe v1) (coe v2) (coe v5) (coe v8)
      MAlonzo.Code.Once.Spec.Module.C_ffi_52 v13 v17 v18 v19 v20
        -> case coe v4 of
             (:) v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v23
                      -> coe
                           du_toProgramFrom_934 (coe v0) (coe v1) (coe v2)
                           (coe
                              MAlonzo.Code.Once.Spec.Module.C_scope_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v23))
                                    (coe v13))
                                 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3)))
                              (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)))
                           (coe v22) (coe v5)
                           (coe
                              C_i'45'ffi_84 v17 v18 v19
                              (coe
                                 v10
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v23))
                                    (coe v13))
                                 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
                              v6)
                           (coe v7) (coe v8) (coe v20)
                           (coe
                              (\ v24 v25 ->
                                 coe
                                   v10 v24
                                   (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v25)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_mono_64 v13 v15 v18 v19 v20
        -> case coe v4 of
             (:) v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v23
                      -> coe
                           du_toProgramFrom_934 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v2
                              (d_monoSchema_8 (coe v13)))
                           (coe
                              MAlonzo.Code.Once.Spec.Module.C_scope_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v23))
                                    (coe v13))
                                 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3)))
                              (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3)))
                           (coe v22)
                           (coe
                              du_monoDef_718 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                              (coe v13) (coe v15) (coe v5) (coe v6) (coe v7) (coe v19))
                           (coe
                              C_i'45'def_94 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkI_130 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                                 (coe v6)))
                           (coe
                              du_wkT_158 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))
                              (coe v7))
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8) (coe v20) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_poly_74 v14 v15 v16
        -> case coe v4 of
             (:) v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v19
                      -> coe
                           du_toProgramFrom_934 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v1))
                           (coe
                              MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v2
                              (MAlonzo.Code.Once.Spec.Core.Schema.d_schemaOf_394
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v19))))
                           (coe
                              MAlonzo.Code.Once.Spec.Module.C_scope_16
                              (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v19)
                                 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))))
                           (coe v18)
                           (coe
                              du_polyDef_758 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v14) (coe v5) (coe v6) (coe v7) (coe v15))
                           (coe
                              du_wkI_130 (coe MAlonzo.Code.Once.Spec.Module.d_imps_12 (coe v3))
                              (coe v6))
                           (coe
                              C_t'45'def_118 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                              (coe
                                 du_wkT_158 (coe MAlonzo.Code.Once.Spec.Module.d_tele_14 (coe v3))
                                 (coe v7)))
                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8) (coe v16) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Translate.toProgram₀
d_toProgram'8320'_1324 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_toProgram'8320'_1324 v0 v1 v2
  = coe
      d_toProgram_822
      (coe
         MAlonzo.Code.Once.Spec.Module.du_teleSig_104 (coe v0) (coe v1))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_'91''93'_868)
      (coe
         MAlonzo.Code.Once.Spec.Module.C_scope_16
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v0) (coe MAlonzo.Code.Once.Spec.Core.Telescope.C_'91''93'_16)
      (coe C_'91''93'_76) (coe C_'91''93'_110) erased (coe v1) (coe v2)
      (coe (\ v3 v4 -> v4))
