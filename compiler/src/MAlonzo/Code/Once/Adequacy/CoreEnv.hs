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
import qualified MAlonzo.Code.Once.Adequacy.CoreMeaningBridge
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Internal.Contract
import qualified MAlonzo.Code.Once.Internal.Core.Meaning
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Core.Translate
import qualified MAlonzo.Code.Once.Internal.Elaboration
import qualified MAlonzo.Code.Once.Internal.Name
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.CoreEnv.GM.DefSem
d_DefSem_16 a0 a1 a2 a3 = ()
-- Once.Adequacy.CoreEnv.GM.DefSem.defs
d_defs_34 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  AgdaAny
d_defs_34 v0
  = coe MAlonzo.Code.Once.Internal.Core.Meaning.d_defs_374 (coe v0)
-- Once.Adequacy.CoreEnv.GM.DefSem.impl
d_impl_36 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Once.Internal.Contract.T_Impl_242
d_impl_36 v0
  = coe MAlonzo.Code.Once.Internal.Core.Meaning.d_impl_376 (coe v0)
-- Once.Adequacy.CoreEnv._.Agree
d_Agree_54 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.Adequacy.CoreEnv._.impSem
d_impSem_58 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 -> AgdaAny
d_impSem_58 ~v0 ~v1 ~v2 ~v3 = du_impSem_58
du_impSem_58 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 -> AgdaAny
du_impSem_58 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_impSem_120 v0 v3
-- Once.Adequacy.CoreEnv._.refSem
d_refSem_60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_refSem_60 ~v0 ~v1 ~v2 ~v3 = du_refSem_60
du_refSem_60 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_refSem_60 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_100 v0 v1 v3
-- Once.Adequacy.CoreEnv._.Agree.agree-ground
d_agree'45'ground_64 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ground_64 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-import
d_agree'45'import_66 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'import_66 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-inst
d_agree'45'inst_68 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'inst_68 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-resolved
d_agree'45'resolved_70 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'resolved_70 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-world
d_agree'45'world_72 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'world_72 = erased
-- Once.Adequacy.CoreEnv._.impEnv
d_impEnv_82 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 -> AgdaAny
d_impEnv_82 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_impEnv_82 v4 v5 v6
du_impEnv_82 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 -> AgdaAny
du_impEnv_82 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Core.Translate.C_'91''93'_92
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Internal.Core.Translate.C_i'45'def_102 v6 v8
        -> case coe v1 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_100 (coe v0)
                       (coe v6)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.Translate.du_mono'45'inst_276))
                    (coe du_impEnv_82 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.defEnv
d_defEnv_92 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 -> AgdaAny
d_defEnv_92 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_defEnv_92 v4 v5 v6
du_defEnv_92 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 -> AgdaAny
du_defEnv_92 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Core.Translate.C_'91''93'_118
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Internal.Core.Translate.C_t'45'def_126 v5 v7
        -> case coe v1 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       (\ v10 v11 ->
                          coe
                            MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_100 (coe v0)
                            (coe v5)
                            (coe
                               MAlonzo.Code.Once.Internal.Core.Translate.du_poly'45'inst_294
                               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v8)) (coe v11))))
                    (coe du_defEnv_92 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.agree-imp
d_agree'45'imp_116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'imp_116 = erased
-- Once.Adequacy.CoreEnv._.agree-def
d_agree'45'def_208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'def_208 = erased
-- Once.Adequacy.CoreEnv._.envOf
d_envOf_306 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
d_envOf_306 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_envOf_306 v1 v4 v5 v6 v7 v8 v9 v10
du_envOf_306 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294
du_envOf_306 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.C_meanings_326
      (coe du_defEnv_92 (coe v1) (coe v4) (coe v7))
      (coe du_impEnv_82 (coe v1) (coe v3) (coe v6))
      (coe
         MAlonzo.Code.Once.Internal.Trace.C_interp_192 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Core.Meaning.d_impl_376 (coe v1)))
      (coe
         (\ v8 v9 v10 ->
            MAlonzo.Code.Once.Internal.Elaboration.d_member_486
              (coe
                 MAlonzo.Code.Once.Internal.Core.Translate.du_sigAt_396 (coe v2)
                 (coe v5)
                 (coe MAlonzo.Code.Once.Internal.Name.d_showCanonical_6 (coe v8)))))
-- Once.Adequacy.CoreEnv._.agree
d_agree_328 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140
d_agree_328 = erased
