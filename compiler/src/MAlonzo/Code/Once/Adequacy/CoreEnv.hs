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
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Adequacy.CoreMeaningBridge
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.GradedOps
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
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

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
-- Once.Adequacy.CoreEnv._.ImportAt
d_ImportAt_40 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.CoreEnv._.Agree
d_Agree_54 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.CoreEnv._.impSem
d_impSem_58 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 -> AgdaAny
d_impSem_58 v0 v1 ~v2 ~v3 = du_impSem_58 v0 v1
du_impSem_58 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 -> AgdaAny
du_impSem_58 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_impSem_110 (coe v0)
      (coe v1)
-- Once.Adequacy.CoreEnv._.refSem
d_refSem_60 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_refSem_60 ~v0 ~v1 ~v2 ~v3 = du_refSem_60
du_refSem_60 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_refSem_60 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_90 v0 v1 v3
-- Once.Adequacy.CoreEnv._.Agree.agree-ground
d_agree'45'ground_64 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ground_64 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-import
d_agree'45'import_66 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'import_66 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-inst
d_agree'45'inst_68 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'inst_68 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-qualified
d_agree'45'qualified_70 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'qualified_70 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-resolved
d_agree'45'resolved_72 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'resolved_72 = erased
-- Once.Adequacy.CoreEnv._.Agree.agree-world
d_agree'45'world_74 ::
  MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'world_74 = erased
-- Once.Adequacy.CoreEnv.notOwn-invalid
d_notOwn'45'invalid_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_notOwn'45'invalid_78 = erased
-- Once.Adequacy.CoreEnv._.impEnv
d_impEnv_94 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 -> AgdaAny
d_impEnv_94 v0 v1 ~v2 ~v3 v4 v5 v6 = du_impEnv_94 v0 v1 v4 v5 v6
du_impEnv_94 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 -> AgdaAny
du_impEnv_94 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Core.Translate.C_'91''93'_76
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Core.Translate.C_i'45'ffi_84 v8 v9 v10 v11 v12
        -> case coe v3 of
             (:) v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Denotation.GradedOps.du_sigOpRef'7515'_514
                              (coe v16) (coe v0) (coe v1)
                              (coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_356 (coe v2))
                              (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v15)) (coe v8))
                           (coe du_impEnv_94 (coe v0) (coe v1) (coe v2) (coe v14) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Translate.C_i'45'def_94 v8 v10
        -> case coe v3 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_90 (coe v2)
                       (coe v8)
                       (coe MAlonzo.Code.Once.Spec.Core.Translate.du_mono'45'inst_240))
                    (coe du_impEnv_94 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.defEnv
d_defEnv_114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_102 -> AgdaAny
d_defEnv_114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_defEnv_114 v4 v5 v6
du_defEnv_114 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_102 -> AgdaAny
du_defEnv_114 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Core.Translate.C_'91''93'_110
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Core.Translate.C_t'45'def_118 v5 v7
        -> case coe v1 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       (\ v10 v11 ->
                          coe
                            MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.du_refSem_90 (coe v0)
                            (coe v5)
                            (coe
                               MAlonzo.Code.Once.Spec.Core.Translate.du_poly'45'inst_258
                               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v8)) (coe v11))))
                    (coe du_defEnv_114 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.agree-imp
d_agree'45'imp_140 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'imp_140 = erased
-- Once.Adequacy.CoreEnv._.agree-def
d_agree'45'def_340 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_102 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'def_340 = erased
-- Once.Adequacy.CoreEnv._.DefsValid
d_DefsValid_434 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 -> ()
d_DefsValid_434 = erased
-- Once.Adequacy.CoreEnv._.IsFFI
d_IsFFI_446 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 -> ()
d_IsFFI_446 = erased
-- Once.Adequacy.CoreEnv._.lookup-ffi
d_lookup'45'ffi_458 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_lookup'45'ffi_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9 ~v10 ~v11
  = du_lookup'45'ffi_458 v5 v6 v7 v8
du_lookup'45'ffi_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_lookup'45'ffi_458 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Core.Translate.C_i'45'ffi_84 v7 v8 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> let v16
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v16 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v14))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                      (coe v14) (coe v3)) in
                         coe
                           (case coe v16 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                -> if coe v17
                                     then coe
                                            seq (coe v18)
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     else coe
                                            seq (coe v18)
                                            (coe
                                               du_lookup'45'ffi_458 (coe v13) (coe v11) (coe v2)
                                               (coe v3))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Translate.C_i'45'def_94 v7 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> let v16
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v16 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v12))
                                          (coe
                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                             (coe v12) (coe v3)) in
                                coe
                                  (case coe v16 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                       -> coe
                                            seq (coe v17)
                                            (coe
                                               seq (coe v18)
                                               (coe
                                                  du_lookup'45'ffi_458 (coe v11) (coe v9) (coe v15)
                                                  (coe v3)))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.ffi-mem
d_ffi'45'mem_666 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ffi'45'mem_666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_ffi'45'mem_666 v7
du_ffi'45'mem_666 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_ffi'45'mem_666 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Elaboration.C_ffi_458 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreEnv._.envOf
d_envOf_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_102 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_302
d_envOf_676 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 ~v9
  = du_envOf_676 v0 v1 v4 v5 v6 v7 v8
du_envOf_676 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_102 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_302
du_envOf_676 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Denotation.Meaning.C_meanings_348
      (coe du_defEnv_114 (coe v2) (coe v4) (coe v6))
      (coe du_impEnv_94 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_468 (coe v1)
         (coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_356 (coe v2)))
      (coe
         (\ v7 v8 v9 v10 ->
            coe
              du_ffi'45'mem_666
              (coe
                 MAlonzo.Code.Once.Spec.Core.Translate.du_impAt_280 (coe v3)
                 (coe v5)
                 (coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v8
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("." :: Data.Text.Text) v7)))))
      (coe
         (\ v7 v8 v9 v10 ->
            coe
              du_ffi'45'mem_666
              (coe
                 MAlonzo.Code.Once.Spec.Core.Translate.du_impAt_280 (coe v3)
                 (coe v5)
                 (coe
                    MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v7)))))
-- Once.Adequacy.CoreEnv._.ffi-sem
d_ffi'45'sem_706 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ffi'45'sem_706 = erased
-- Once.Adequacy.CoreEnv._.agree
d_agree_724 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_ImpSig_68 ->
  MAlonzo.Code.Once.Spec.Core.Translate.T_TeleSig_102 ->
  AgdaAny -> MAlonzo.Code.Once.Adequacy.CoreMeaningBridge.T_Agree_140
d_agree_724 = erased
