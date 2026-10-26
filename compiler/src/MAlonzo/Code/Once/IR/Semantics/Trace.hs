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

module MAlonzo.Code.Once.IR.Semantics.Trace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Contract
import qualified MAlonzo.Code.Once.IR.Semantics.Event
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.IR.Semantics.Trace.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'base'45'to'45'full_422
      v2 v3 v4
-- Once.IR.Semantics.Trace.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_12 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.IR.Semantics.Trace.M.coerce-functor
d_coerce'45'functor_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.IR.Semantics.Trace.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.IR.Semantics.Trace.M.coerce-μ-in
d_coerce'45'μ'45'in_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.IR.Semantics.Trace.M.coerce-μ-out
d_coerce'45'μ'45'out_20 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_20 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'out_502 v2
      v3 v5
-- Once.IR.Semantics.Trace.M.coerce-ν-in
d_coerce'45'ν'45'in_22 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_22 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.IR.Semantics.Trace.M.coerce-ν-out
d_coerce'45'ν'45'out_24 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_24 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.IR.Semantics.Trace.M.eraseᵍ
d_erase'7501'_26 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_26 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.IR.Semantics.Trace.M.sem-CoIn
d_sem'45'CoIn_28 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_28 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.IR.Semantics.Trace.M.sem-CoOut
d_sem'45'CoOut_30 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_30 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoOut_636 v2 v3 v4
-- Once.IR.Semantics.Trace.M.sem-In
d_sem'45'In_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_32 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.IR.Semantics.Trace.M.sem-Out
d_sem'45'Out_34 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'Out_556 v2 v3 v4
-- Once.IR.Semantics.Trace.M.sem-ana
d_sem'45'ana_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.IR.Semantics.Trace.M.sem-cata
d_sem'45'cata_38 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_38 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'cata_572 v2 v3 v5
-- Once.IR.Semantics.Trace.M.sem-fmap
d_sem'45'fmap_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_40 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.IR.Semantics.Trace.M.sem-para
d_sem'45'para_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_42 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'para_592 v2 v3 v5 v6
-- Once.IR.Semantics.Trace.M.semAnaLayer
d_semAnaLayer_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.IR.Semantics.Trace.M.sfmapSemAna
d_sfmapSemAna_46 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_46 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sfmapSemAna_678 v0 v1 v2 v4
      v5
-- Once.IR.Semantics.Trace.M.⟦_⟧
d_'10214'_'10215'_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_48 = erased
-- Once.IR.Semantics.Trace.M.⟦_⟧F
d_'10214'_'10215'F_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_50 = erased
-- Once.IR.Semantics.Trace.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_52 = erased
-- Once.IR.Semantics.Trace.M.⟦μ⟧
d_'10214'μ'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_54 = erased
-- Once.IR.Semantics.Trace.M.⟦ν⟧
d_'10214'ν'10215'_56 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_56 = erased
-- Once.IR.Semantics.Trace.CallOp
d_CallOp_58 = ()
data T_CallOp_58
  = C_callOp_76 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Type.T_Base_84
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
-- Once.IR.Semantics.Trace.CallOp.cname
d_cname_68 ::
  T_CallOp_58 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_cname_68 v0
  = case coe v0 of
      C_callOp_76 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.CallOp.cdom
d_cdom_70 :: T_CallOp_58 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_cdom_70 v0
  = case coe v0 of
      C_callOp_76 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.CallOp.cbase
d_cbase_72 :: T_CallOp_58 -> MAlonzo.Code.Once.Spec.Type.T_Base_84
d_cbase_72 v0
  = case coe v0 of
      C_callOp_76 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.CallOp.ccod
d_ccod_74 :: T_CallOp_58 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_ccod_74 v0
  = case coe v0 of
      C_callOp_76 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.HaltOp
d_HaltOp_78 = ()
data T_HaltOp_78
  = C_haltOp_92 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Type.T_Base_84
-- Once.IR.Semantics.Trace.HaltOp.hname
d_hname_86 ::
  T_HaltOp_78 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_hname_86 v0
  = case coe v0 of
      C_haltOp_92 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.HaltOp.hdom
d_hdom_88 :: T_HaltOp_78 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_hdom_88 v0
  = case coe v0 of
      C_haltOp_92 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.HaltOp.hbase
d_hbase_90 :: T_HaltOp_78 -> MAlonzo.Code.Once.Spec.Type.T_Base_84
d_hbase_90 v0
  = case coe v0 of
      C_haltOp_92 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.callEvent
d_callEvent_96 ::
  T_CallOp_58 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58
d_callEvent_96 v0 v1
  = coe
      MAlonzo.Code.Once.IR.Semantics.Event.C_mk'45'event_76
      (d_cname_68 (coe v0)) (d_cdom_70 (coe v0)) v1
-- Once.IR.Semantics.Trace.haltEvent
d_haltEvent_104 ::
  T_HaltOp_78 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58
d_haltEvent_104 v0 v1
  = coe
      MAlonzo.Code.Once.IR.Semantics.Event.C_mk'45'event_76
      (d_hname_86 (coe v0)) (d_hdom_88 (coe v0)) v1
-- Once.IR.Semantics.Trace.T
d_T_112 a0 = ()
data T_T_112
  = C_ret_116 AgdaAny |
    C_call_120 T_CallOp_58 AgdaAny (AgdaAny -> T_T_112) |
    C_halt_124 T_HaltOp_78 AgdaAny
-- Once.IR.Semantics.Trace.returnT
d_returnT_128 :: () -> AgdaAny -> T_T_112
d_returnT_128 ~v0 = du_returnT_128
du_returnT_128 :: AgdaAny -> T_T_112
du_returnT_128 = coe C_ret_116
-- Once.IR.Semantics.Trace._>>=T_
d__'62''62''61'T__134 ::
  () -> () -> T_T_112 -> (AgdaAny -> T_T_112) -> T_T_112
d__'62''62''61'T__134 ~v0 ~v1 v2 v3 = du__'62''62''61'T__134 v2 v3
du__'62''62''61'T__134 ::
  T_T_112 -> (AgdaAny -> T_T_112) -> T_T_112
du__'62''62''61'T__134 v0 v1
  = case coe v0 of
      C_ret_116 v2 -> coe v1 v2
      C_call_120 v2 v3 v4
        -> coe
             C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du__'62''62''61'T__134 (coe v4 v5) (coe v1)))
      C_halt_124 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace._>>T_
d__'62''62'T__160 :: () -> () -> T_T_112 -> T_T_112 -> T_T_112
d__'62''62'T__160 ~v0 ~v1 v2 v3 = du__'62''62'T__160 v2 v3
du__'62''62'T__160 :: T_T_112 -> T_T_112 -> T_T_112
du__'62''62'T__160 v0 v1
  = coe du__'62''62''61'T__134 (coe v0) (coe (\ v2 -> v1))
-- Once.IR.Semantics.Trace.fmapT
d_fmapT_172 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T_112 -> T_T_112
d_fmapT_172 ~v0 ~v1 v2 v3 = du_fmapT_172 v2 v3
du_fmapT_172 :: (AgdaAny -> AgdaAny) -> T_T_112 -> T_T_112
du_fmapT_172 v0 v1
  = coe
      du__'62''62''61'T__134 (coe v1)
      (coe (\ v2 -> coe C_ret_116 (coe v0 v2)))
-- Once.IR.Semantics.Trace.callKey
d_callKey_180 :: T_CallOp_58 -> MAlonzo.Code.Once.Contract.T_Key_54
d_callKey_180 v0
  = coe
      MAlonzo.Code.Once.Contract.C_key_68
      (coe
         MAlonzo.Code.Once.Name.d_showCanonical_4 (coe d_cname_68 (coe v0)))
      (coe d_cdom_70 (coe v0)) (coe d_ccod_74 (coe v0))
-- Once.IR.Semantics.Trace.Interp
d_Interp_184 = ()
data T_Interp_184
  = C_interp_194 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 MAlonzo.Code.Once.Contract.T_Impl_240
-- Once.IR.Semantics.Trace.Interp.sig
d_sig_190 ::
  T_Interp_184 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sig_190 v0
  = case coe v0 of
      C_interp_194 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.Interp.impl
d_impl_192 :: T_Interp_184 -> MAlonzo.Code.Once.Contract.T_Impl_240
d_impl_192 v0
  = case coe v0 of
      C_interp_194 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.calls
d_calls_196 ::
  T_Interp_184 -> [MAlonzo.Code.Once.Contract.T_Key_54]
d_calls_196 v0
  = coe
      MAlonzo.Code.Once.Contract.d_answerKeys_224
      (coe d_sig_190 (coe v0))
-- Once.IR.Semantics.Trace.pures
d_pures_198 ::
  T_Interp_184 -> [MAlonzo.Code.Once.Contract.T_Key_54]
d_pures_198 v0
  = coe
      MAlonzo.Code.Once.Contract.d_valueKeys_222 (coe d_sig_190 (coe v0))
-- Once.IR.Semantics.Trace.answer
d_answer_208 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_CallOp_58 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_answer_208 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Contract.d_answerI_254 (d_impl_192 (coe v0)) v1
      (d_callKey_180 (coe v2)) v3
-- Once.IR.Semantics.Trace.pure
d_pure_222 ::
  T_Interp_184 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_pure_222 v0
  = coe
      MAlonzo.Code.Once.Contract.d_pureI_258 (coe d_impl_192 (coe v0))
-- Once.IR.Semantics.Trace.unlinkedOp
d_unlinkedOp_226 :: T_HaltOp_78
d_unlinkedOp_226
  = coe
      C_haltOp_92
      (coe
         MAlonzo.Code.Once.Spec.Name.C_canonical_12
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe ("Generators" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe ("unlinked" :: Data.Text.Text))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
-- Once.IR.Semantics.Trace.unlinkedT
d_unlinkedT_230 :: () -> T_T_112
d_unlinkedT_230 ~v0 = du_unlinkedT_230
du_unlinkedT_230 :: T_T_112
du_unlinkedT_230
  = coe
      C_halt_124 (coe d_unlinkedOp_226)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.IR.Semantics.Trace.resT
d_resT_234 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> T_T_112
d_resT_234 ~v0 v1 = du_resT_234 v1
du_resT_234 :: MAlonzo.Code.Once.Res.T_Res_6 -> T_T_112
du_resT_234 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe du_unlinkedT_230
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe C_ret_116 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.pureHalf-at
d_pureHalf'45'at_242 ::
  T_Interp_184 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_pureHalf'45'at_242 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe
                           MAlonzo.Code.Once.Res.C_returns_12 (coe d_pure_222 v0 v1 v6 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.FFIAnswers
d_FFIAnswers_258 :: ()
d_FFIAnswers_258 = erased
-- Once.IR.Semantics.Trace.pureHalf
d_pureHalf_264 ::
  T_Interp_184 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_pureHalf_264 v0 v1 v2 v3
  = coe
      d_pureHalf'45'at_242 (coe v0)
      (coe
         MAlonzo.Code.Once.Contract.C_key_68
         (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v1)) (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Once.Contract.d__'8712'K'63'__106
         (coe
            MAlonzo.Code.Once.Contract.C_key_68
            (coe MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v1)) (coe v2)
            (coe v3))
         (d_pures_198 (coe v0)))
-- Once.IR.Semantics.Trace.Run
d_Run_274 :: () -> ()
d_Run_274 = erased
-- Once.IR.Semantics.Trace.consE
d_consE_280 ::
  () ->
  MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consE_280 ~v0 v1 v2 = du_consE_280 v1 v2
du_consE_280 ::
  MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consE_280 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.IR.Semantics.Trace.appE
d_appE_288 ::
  () ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appE_288 ~v0 v1 v2 = du_appE_288 v1 v2
du_appE_288 ::
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appE_288 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.IR.Semantics.Trace.callAnswer-at
d_callAnswer'45'at_298 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_CallOp_58 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny
d_callAnswer'45'at_298 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v7)
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe d_answer_208 v0 v1 v2 v10 v3)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.callAnswer
d_callAnswer_332 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_CallOp_58 -> AgdaAny -> Maybe AgdaAny
d_callAnswer_332 v0 v1 v2 v3
  = coe
      d_callAnswer'45'at_298 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64
         (coe d_ccod_74 (coe v2)))
      (coe
         MAlonzo.Code.Once.Contract.d__'8712'K'63'__106
         (d_callKey_180 (coe v2)) (d_calls_196 (coe v0)))
-- Once.IR.Semantics.Trace.run
d_run_344 ::
  () ->
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_T_112 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run_344 ~v0 v1 v2 v3 = du_run_344 v1 v2 v3
du_run_344 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_T_112 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run_344 v0 v1 v2
  = case coe v2 of
      C_ret_116 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Res.C_returns_12 (coe v3))
      C_call_120 v3 v4 v5
        -> coe
             du_run'45'call_352 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe d_callAnswer_332 (coe v0) (coe v1) (coe v3) (coe v4))
      C_halt_124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe d_haltEvent_104 (coe v3) (coe v4)))
             (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.run-call
d_run'45'call_352 ::
  () ->
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_CallOp_58 ->
  AgdaAny ->
  (AgdaAny -> T_T_112) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'call_352 ~v0 v1 v2 v3 v4 v5 v6
  = du_run'45'call_352 v1 v2 v3 v4 v5 v6
du_run'45'call_352 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_CallOp_58 ->
  AgdaAny ->
  (AgdaAny -> T_T_112) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'call_352 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_consE_280 (coe d_callEvent_96 (coe v2) (coe v3))
             (coe
                du_run_344 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe d_callEvent_96 (coe v2) (coe v3))))
                (coe v4 v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   d_haltEvent_104 (coe d_unlinkedOp_226)
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.thenRes
d_thenRes_404 ::
  () ->
  () ->
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_112) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thenRes_404 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_thenRes_404 v2 v3 v4 v5 v6
du_thenRes_404 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_112) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thenRes_404 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      MAlonzo.Code.Once.Res.C_returns_12 v5
        -> coe
             du_appE_288 (coe v2)
             (coe
                du_run_344 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
                (coe v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.then
d_then_428 ::
  () ->
  () ->
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_T_112) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_then_428 ~v0 ~v1 v2 v3 v4 v5 = du_then_428 v2 v3 v4 v5
du_then_428 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_T_112) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_then_428 v0 v1 v2 v3
  = coe
      du_thenRes_404 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) (coe v3)
-- Once.IR.Semantics.Trace.eventsT
d_eventsT_440 ::
  () ->
  T_Interp_184 ->
  T_T_112 -> [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_eventsT_440 ~v0 v1 v2 = du_eventsT_440 v1 v2
du_eventsT_440 ::
  T_Interp_184 ->
  T_T_112 -> [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_eventsT_440 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_run_344 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
-- Once.IR.Semantics.Trace.projTrace
d_projTrace_448 ::
  () ->
  T_Interp_184 ->
  T_T_112 ->
  Integer -> [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
d_projTrace_448 ~v0 v1 v2 v3 = du_projTrace_448 v1 v2 v3
du_projTrace_448 ::
  T_Interp_184 ->
  T_T_112 ->
  Integer -> [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]
du_projTrace_448 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v2)
      (coe du_eventsT_440 (coe v0) (coe v1))
-- Once.IR.Semantics.Trace.Bounded
d_Bounded_456 ::
  (Integer ->
   [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]) ->
  ()
d_Bounded_456 = erased
-- Once.IR.Semantics.Trace.Saturating
d_Saturating_462 ::
  (Integer ->
   [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]) ->
  ()
d_Saturating_462 = erased
-- Once.IR.Semantics.Trace.Coherent
d_Coherent_468 ::
  (Integer ->
   [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58]) ->
  ()
d_Coherent_468 = erased
-- Once.IR.Semantics.Trace.PrefixFamily
d_PrefixFamily_478 a0 = ()
data T_PrefixFamily_478
  = C_prefixFamily_494 (Integer ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.IR.Semantics.Trace.PrefixFamily.bnd
d_bnd_488 ::
  T_PrefixFamily_478 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_488 v0
  = case coe v0 of
      C_prefixFamily_494 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.PrefixFamily.sat
d_sat_490 ::
  T_PrefixFamily_478 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_490 = erased
-- Once.IR.Semantics.Trace.PrefixFamily.coh
d_coh_492 ::
  T_PrefixFamily_478 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh_492 v0
  = case coe v0 of
      C_prefixFamily_494 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.Returns?
d_Returns'63'_498 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_Returns'63'_498 = erased
-- Once.IR.Semantics.Trace.resVal
d_resVal_504 ::
  () -> MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny -> AgdaAny
d_resVal_504 ~v0 v1 ~v2 = du_resVal_504 v1
du_resVal_504 :: MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_resVal_504 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Trace.resultAt
d_resultAt_510 ::
  () ->
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_T_112 -> MAlonzo.Code.Once.Res.T_Res_6
d_resultAt_510 ~v0 v1 v2 v3 = du_resultAt_510 v1 v2 v3
du_resultAt_510 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_T_112 -> MAlonzo.Code.Once.Res.T_Res_6
du_resultAt_510 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_run_344 (coe v0) (coe v1) (coe v2))
-- Once.IR.Semantics.Trace.valueT
d_valueT_528 ::
  () ->
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_T_112 -> AgdaAny -> AgdaAny
d_valueT_528 ~v0 v1 v2 v3 ~v4 = du_valueT_528 v1 v2 v3
du_valueT_528 ::
  T_Interp_184 ->
  [MAlonzo.Code.Once.IR.Semantics.Event.T_SigOpEvent_58] ->
  T_T_112 -> AgdaAny
du_valueT_528 v0 v1 v2
  = coe
      du_resVal_504 (coe du_resultAt_510 (coe v0) (coe v1) (coe v2))
-- Once.IR.Semantics.Trace.RelT′
d_RelT'8242'_544 a0 a1 a2 a3 a4 = ()
data T_RelT'8242'_544
  = C_rel'45'ret_556 AgdaAny |
    C_rel'45'call_568 (AgdaAny -> T_RelT'8242'_544) | C_rel'45'halt_574
