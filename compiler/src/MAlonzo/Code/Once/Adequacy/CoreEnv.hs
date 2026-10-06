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

module MAlonzo.Code.Once.Adequacy.CoreEnv where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Adequacy.CoreMeaningBridge
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.Meaning
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Translate
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CoreEnv.GM.DefSem
d_DefSem_16 a0 a1 a2 a3 = ()
-- Once.Adequacy.CoreEnv.GM.DefSem.defs
d_defs_34 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  AgdaAny
d_defs_34 v0
  = coe MAlonzo.Code.Once.Spec.Core.Meaning.d_defs_354 (coe v0)
-- Once.Adequacy.CoreEnv.GM.DefSem.impl
d_impl_36 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408
d_impl_36 v0
  = coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_356 (coe v0)
-- Once.Adequacy.CoreEnv._.Agree
d_Agree_66 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.CoreEnv._.impSem
d_impSem_70 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_476 -> AgdaAny
d_impSem_70 ~v0 ~v1 ~v2 ~v3 = du_impSem_70
du_impSem_70 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_476 -> AgdaAny
du_impSem_70 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_impSem_124 v0 v3
-- Once.Adequacy.CoreEnv._.refSem
d_refSem_72 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_refSem_72 ~v0 ~v1 ~v2 ~v3 = du_refSem_72
du_refSem_72 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_refSem_72 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_104 v0 v1 v3
-- Once.Adequacy.CoreEnv._.Agree.agree-ground
d_agree'45'ground_76 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ground_76 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-import
d_agree'45'import_78 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'import_78 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-inst
d_agree'45'inst_80 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'inst_80 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-qualified
d_agree'45'qualified_82 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'qualified_82 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-resolved
d_agree'45'resolved_84 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'resolved_84 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-world
d_agree'45'world_86 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'world_86 = erased
-- Once.Adequacy.CoreEnv._.impEnv
d_impEnv_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 -> AgdaAny
d_impEnv_96 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_impEnv_96 v4 v5 v6
du_impEnv_96 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 -> AgdaAny
du_impEnv_96 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.Translate.C_'91''93'_92
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Core.Translate.C_i'45'def_102 v6 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_104 (coe v0)
                       (coe v6)
                       (coe MAlonzo.Code.Once.Spec.Core.Translate.du_mono'45'inst_256))
                    (coe du_impEnv_96 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.defEnv
d_defEnv_106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 -> AgdaAny
d_defEnv_106 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_defEnv_106 v4 v5 v6
du_defEnv_106 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 -> AgdaAny
du_defEnv_106 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.Translate.C_'91''93'_118
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Core.Translate.C_t'45'def_126 v5 v7
        -> case coe v1 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       (\ v10 v11 ->
                          coe
                            MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_104 (coe v0)
                            (coe v5)
                            (coe
                               MAlonzo.Code.Once.Spec.Core.Translate.du_poly'45'inst_274
                               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v8)) (coe v11))))
                    (coe du_defEnv_106 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.agree-imp
d_agree'45'imp_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'imp_130 = erased
-- Once.Adequacy.CoreEnv._.agree-def
d_agree'45'def_222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'def_222 = erased
-- Once.Adequacy.CoreEnv._.envOf
d_envOf_320 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_304
d_envOf_320 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_envOf_320 v1 v4 v5 v6 v7 v8 v9 v10
du_envOf_320 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_304
du_envOf_320 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.C_meanings_352
      (coe du_defEnv_106 (coe v1) (coe v4) (coe v7))
      (coe du_impEnv_96 (coe v1) (coe v3) (coe v6))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_468 (coe v0)
         (coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_356 (coe v1)))
      (coe
         (\ v8 v9 v10 v11 ->
            MAlonzo.Code.Once.Spec.Elaboration.d_member_468
              (coe
                 MAlonzo.Code.Once.Spec.Core.Translate.du_sigAt_376 (coe v2)
                 (coe v5)
                 (coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("." :: Data.Text.Text) v8)))))
      (coe
         (\ v8 v9 v10 ->
            MAlonzo.Code.Once.Spec.Elaboration.d_member_468
              (coe
                 MAlonzo.Code.Once.Spec.Core.Translate.du_sigAt_376 (coe v2)
                 (coe v5)
                 (coe
                    MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v8)))))
-- Once.Adequacy.CoreEnv._.agree
d_agree_344 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_144
d_agree_344 = erased
