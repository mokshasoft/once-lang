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

module MAlonzo.Code.Once.Internal.Trace where

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
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Internal.Trace.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_420
      v2 v3 v4
-- Once.Internal.Trace.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_384
      v1 v2
-- Once.Internal.Trace.M.coerce-functor
d_coerce'45'functor_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_252 v1 v3
-- Once.Internal.Trace.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_296
      v1 v3
-- Once.Internal.Trace.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_454 v1 v3
-- Once.Internal.Trace.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_500 v2 v3 v5
-- Once.Internal.Trace.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20 v0
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616
-- Once.Internal.Trace.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_626 v2
-- Once.Internal.Trace.M.eraseᵍ
d_erase'7501'_24 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_110 v1 v2
-- Once.Internal.Trace.M.sem-CoIn
d_sem'45'CoIn_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
d_sem'45'CoIn_26 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_646 v1 v2
-- Once.Internal.Trace.M.sem-CoOut
d_sem'45'CoOut_28 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_16 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_28 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_634 v2 v3 v4
-- Once.Internal.Trace.M.sem-In
d_sem'45'In_30 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_30 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_542 v1 v2
-- Once.Internal.Trace.M.sem-Out
d_sem'45'Out_32 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_554 v2 v3 v4
-- Once.Internal.Trace.M.sem-ana
d_sem'45'ana_34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
d_sem'45'ana_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_658 v0 v1 v3 v4
-- Once.Internal.Trace.M.sem-cata
d_sem'45'cata_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_570 v2 v3 v5
-- Once.Internal.Trace.M.sem-fmap
d_sem'45'fmap_38 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_342 v1 v4 v5
-- Once.Internal.Trace.M.sem-para
d_sem'45'para_40 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_590 v2 v3 v5 v6
-- Once.Internal.Trace.M.semAnaLayer
d_semAnaLayer_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_666 v0 v1 v3 v4
-- Once.Internal.Trace.M.sfmapSemAna
d_sfmapSemAna_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_676 v0 v1 v2 v4 v5
-- Once.Internal.Trace.M.⟦_⟧
d_'10214'_'10215'_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Internal.Trace.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Internal.Trace.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Internal.Trace.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Internal.Trace.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Internal.Trace.CallOp
d_CallOp_56 = ()
data T_CallOp_56
  = C_callOp_74 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Type.T_Base_84
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
-- Once.Internal.Trace.CallOp.cname
d_cname_66 ::
  T_CallOp_56 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_cname_66 v0
  = case coe v0 of
      C_callOp_74 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.CallOp.cdom
d_cdom_68 :: T_CallOp_56 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_cdom_68 v0
  = case coe v0 of
      C_callOp_74 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.CallOp.cbase
d_cbase_70 :: T_CallOp_56 -> MAlonzo.Code.Once.Spec.Type.T_Base_84
d_cbase_70 v0
  = case coe v0 of
      C_callOp_74 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.CallOp.ccod
d_ccod_72 :: T_CallOp_56 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_ccod_72 v0
  = case coe v0 of
      C_callOp_74 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.HaltOp
d_HaltOp_76 = ()
data T_HaltOp_76
  = C_haltOp_90 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Type.T_Base_84
-- Once.Internal.Trace.HaltOp.hname
d_hname_84 ::
  T_HaltOp_76 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_hname_84 v0
  = case coe v0 of
      C_haltOp_90 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.HaltOp.hdom
d_hdom_86 :: T_HaltOp_76 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_hdom_86 v0
  = case coe v0 of
      C_haltOp_90 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.HaltOp.hbase
d_hbase_88 :: T_HaltOp_76 -> MAlonzo.Code.Once.Spec.Type.T_Base_84
d_hbase_88 v0
  = case coe v0 of
      C_haltOp_90 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.callEvent
d_callEvent_94 ::
  T_CallOp_56 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56
d_callEvent_94 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Event.C_mk'45'event_74
      (d_cname_66 (coe v0)) (d_cdom_68 (coe v0)) v1
-- Once.Internal.Trace.haltEvent
d_haltEvent_102 ::
  T_HaltOp_76 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56
d_haltEvent_102 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Event.C_mk'45'event_74
      (d_hname_84 (coe v0)) (d_hdom_86 (coe v0)) v1
-- Once.Internal.Trace.T
d_T_110 a0 = ()
data T_T_110
  = C_ret_114 AgdaAny |
    C_call_118 T_CallOp_56 AgdaAny (AgdaAny -> T_T_110) |
    C_halt_122 T_HaltOp_76 AgdaAny
-- Once.Internal.Trace.returnT
d_returnT_126 :: () -> AgdaAny -> T_T_110
d_returnT_126 ~v0 = du_returnT_126
du_returnT_126 :: AgdaAny -> T_T_110
du_returnT_126 = coe C_ret_114
-- Once.Internal.Trace._>>=T_
d__'62''62''61'T__132 ::
  () -> () -> T_T_110 -> (AgdaAny -> T_T_110) -> T_T_110
d__'62''62''61'T__132 ~v0 ~v1 v2 v3 = du__'62''62''61'T__132 v2 v3
du__'62''62''61'T__132 ::
  T_T_110 -> (AgdaAny -> T_T_110) -> T_T_110
du__'62''62''61'T__132 v0 v1
  = case coe v0 of
      C_ret_114 v2 -> coe v1 v2
      C_call_118 v2 v3 v4
        -> coe
             C_call_118 (coe v2) (coe v3)
             (coe (\ v5 -> coe du__'62''62''61'T__132 (coe v4 v5) (coe v1)))
      C_halt_122 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace._>>T_
d__'62''62'T__158 :: () -> () -> T_T_110 -> T_T_110 -> T_T_110
d__'62''62'T__158 ~v0 ~v1 v2 v3 = du__'62''62'T__158 v2 v3
du__'62''62'T__158 :: T_T_110 -> T_T_110 -> T_T_110
du__'62''62'T__158 v0 v1
  = coe du__'62''62''61'T__132 (coe v0) (coe (\ v2 -> v1))
-- Once.Internal.Trace.fmapT
d_fmapT_170 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T_110 -> T_T_110
d_fmapT_170 ~v0 ~v1 v2 v3 = du_fmapT_170 v2 v3
du_fmapT_170 :: (AgdaAny -> AgdaAny) -> T_T_110 -> T_T_110
du_fmapT_170 v0 v1
  = coe
      du__'62''62''61'T__132 (coe v1)
      (coe (\ v2 -> coe C_ret_114 (coe v0 v2)))
-- Once.Internal.Trace.callKey
d_callKey_178 :: T_CallOp_56 -> MAlonzo.Code.Once.Contract.T_Key_54
d_callKey_178 v0
  = coe
      MAlonzo.Code.Once.Contract.C_key_68
      (coe
         MAlonzo.Code.Once.Name.d_showCanonical_4 (coe d_cname_66 (coe v0)))
      (coe d_cdom_68 (coe v0)) (coe d_ccod_72 (coe v0))
-- Once.Internal.Trace.Interp
d_Interp_182 = ()
data T_Interp_182
  = C_interp_192 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 MAlonzo.Code.Once.Contract.T_Impl_240
-- Once.Internal.Trace.Interp.sig
d_sig_188 ::
  T_Interp_182 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sig_188 v0
  = case coe v0 of
      C_interp_192 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.Interp.impl
d_impl_190 :: T_Interp_182 -> MAlonzo.Code.Once.Contract.T_Impl_240
d_impl_190 v0
  = case coe v0 of
      C_interp_192 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.calls
d_calls_194 ::
  T_Interp_182 -> [MAlonzo.Code.Once.Contract.T_Key_54]
d_calls_194 v0
  = coe
      MAlonzo.Code.Once.Contract.d_answerKeys_224
      (coe d_sig_188 (coe v0))
-- Once.Internal.Trace.pures
d_pures_196 ::
  T_Interp_182 -> [MAlonzo.Code.Once.Contract.T_Key_54]
d_pures_196 v0
  = coe
      MAlonzo.Code.Once.Contract.d_valueKeys_222 (coe d_sig_188 (coe v0))
-- Once.Internal.Trace.answer
d_answer_206 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_CallOp_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_answer_206 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Contract.d_answerI_254 (d_impl_190 (coe v0)) v1
      (d_callKey_178 (coe v2)) v3
-- Once.Internal.Trace.pure
d_pure_220 ::
  T_Interp_182 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_pure_220 v0
  = coe
      MAlonzo.Code.Once.Contract.d_pureI_258 (coe d_impl_190 (coe v0))
-- Once.Internal.Trace.unlinkedOp
d_unlinkedOp_224 :: T_HaltOp_76
d_unlinkedOp_224
  = coe
      C_haltOp_90
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
-- Once.Internal.Trace.unlinkedT
d_unlinkedT_228 :: () -> T_T_110
d_unlinkedT_228 ~v0 = du_unlinkedT_228
du_unlinkedT_228 :: T_T_110
du_unlinkedT_228
  = coe
      C_halt_122 (coe d_unlinkedOp_224)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Internal.Trace.resT
d_resT_232 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> T_T_110
d_resT_232 ~v0 v1 = du_resT_232 v1
du_resT_232 :: MAlonzo.Code.Once.Res.T_Res_6 -> T_T_110
du_resT_232 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe du_unlinkedT_228
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe C_ret_114 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.pureHalf-at
d_pureHalf'45'at_240 ::
  T_Interp_182 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_pureHalf'45'at_240 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe
                           MAlonzo.Code.Once.Res.C_returns_12 (coe d_pure_220 v0 v1 v6 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.FFIAnswers
d_FFIAnswers_256 :: ()
d_FFIAnswers_256 = erased
-- Once.Internal.Trace.pureHalf
d_pureHalf_262 ::
  T_Interp_182 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_pureHalf_262 v0 v1 v2 v3
  = coe
      d_pureHalf'45'at_240 (coe v0)
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
         (d_pures_196 (coe v0)))
-- Once.Internal.Trace.Run
d_Run_272 :: () -> ()
d_Run_272 = erased
-- Once.Internal.Trace.consE
d_consE_278 ::
  () ->
  MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consE_278 ~v0 v1 v2 = du_consE_278 v1 v2
du_consE_278 ::
  MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consE_278 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.Internal.Trace.appE
d_appE_286 ::
  () ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appE_286 ~v0 v1 v2 = du_appE_286 v1 v2
du_appE_286 ::
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appE_286 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
-- Once.Internal.Trace.callAnswer-at
d_callAnswer'45'at_296 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_CallOp_56 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe AgdaAny
d_callAnswer'45'at_296 v0 v1 v2 v3 v4 v5
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
                                            (coe d_answer_206 v0 v1 v2 v10 v3)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.callAnswer
d_callAnswer_330 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_CallOp_56 -> AgdaAny -> Maybe AgdaAny
d_callAnswer_330 v0 v1 v2 v3
  = coe
      d_callAnswer'45'at_296 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64
         (coe d_ccod_72 (coe v2)))
      (coe
         MAlonzo.Code.Once.Contract.d__'8712'K'63'__106
         (d_callKey_178 (coe v2)) (d_calls_194 (coe v0)))
-- Once.Internal.Trace.run
d_run_342 ::
  () ->
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_T_110 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run_342 ~v0 v1 v2 v3 = du_run_342 v1 v2 v3
du_run_342 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_T_110 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run_342 v0 v1 v2
  = case coe v2 of
      C_ret_114 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Once.Res.C_returns_12 (coe v3))
      C_call_118 v3 v4 v5
        -> coe
             du_run'45'call_350 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
             (coe d_callAnswer_330 (coe v0) (coe v1) (coe v3) (coe v4))
      C_halt_122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe d_haltEvent_102 (coe v3) (coe v4)))
             (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.run-call
d_run'45'call_350 ::
  () ->
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_run'45'call_350 ~v0 v1 v2 v3 v4 v5 v6
  = du_run'45'call_350 v1 v2 v3 v4 v5 v6
du_run'45'call_350 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> T_T_110) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_run'45'call_350 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_consE_278 (coe d_callEvent_94 (coe v2) (coe v3))
             (coe
                du_run_342 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe d_callEvent_94 (coe v2) (coe v3))))
                (coe v4 v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   d_haltEvent_102 (coe d_unlinkedOp_224)
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe MAlonzo.Code.Once.Res.C_stopped_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.thenRes
d_thenRes_402 ::
  () ->
  () ->
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_110) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_thenRes_402 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_thenRes_402 v2 v3 v4 v5 v6
du_thenRes_402 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> T_T_110) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_thenRes_402 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      MAlonzo.Code.Once.Res.C_returns_12 v5
        -> coe
             du_appE_286 (coe v2)
             (coe
                du_run_342 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
                (coe v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.then
d_then_426 ::
  () ->
  () ->
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_T_110) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_then_426 ~v0 ~v1 v2 v3 v4 v5 = du_then_426 v2 v3 v4 v5
du_then_426 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_T_110) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_then_426 v0 v1 v2 v3
  = coe
      du_thenRes_402 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) (coe v3)
-- Once.Internal.Trace.eventsT
d_eventsT_438 ::
  () ->
  T_Interp_182 ->
  T_T_110 -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_eventsT_438 ~v0 v1 v2 = du_eventsT_438 v1 v2
du_eventsT_438 ::
  T_Interp_182 ->
  T_T_110 -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
du_eventsT_438 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_run_342 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
-- Once.Internal.Trace.projTrace
d_projTrace_446 ::
  () ->
  T_Interp_182 ->
  T_T_110 ->
  Integer -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
d_projTrace_446 ~v0 v1 v2 v3 = du_projTrace_446 v1 v2 v3
du_projTrace_446 ::
  T_Interp_182 ->
  T_T_110 ->
  Integer -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]
du_projTrace_446 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v2)
      (coe du_eventsT_438 (coe v0) (coe v1))
-- Once.Internal.Trace.Bounded
d_Bounded_454 ::
  (Integer -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  ()
d_Bounded_454 = erased
-- Once.Internal.Trace.Saturating
d_Saturating_460 ::
  (Integer -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  ()
d_Saturating_460 = erased
-- Once.Internal.Trace.Coherent
d_Coherent_466 ::
  (Integer -> [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56]) ->
  ()
d_Coherent_466 = erased
-- Once.Internal.Trace.PrefixFamily
d_PrefixFamily_476 a0 = ()
data T_PrefixFamily_476
  = C_prefixFamily_492 (Integer ->
                        MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                       (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Internal.Trace.PrefixFamily.bnd
d_bnd_486 ::
  T_PrefixFamily_476 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_bnd_486 v0
  = case coe v0 of
      C_prefixFamily_492 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.PrefixFamily.sat
d_sat_488 ::
  T_PrefixFamily_476 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat_488 = erased
-- Once.Internal.Trace.PrefixFamily.coh
d_coh_490 ::
  T_PrefixFamily_476 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coh_490 v0
  = case coe v0 of
      C_prefixFamily_492 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.Returns?
d_Returns'63'_496 :: () -> MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_Returns'63'_496 = erased
-- Once.Internal.Trace.resVal
d_resVal_502 ::
  () -> MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny -> AgdaAny
d_resVal_502 ~v0 v1 ~v2 = du_resVal_502 v1
du_resVal_502 :: MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
du_resVal_502 v0
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_returns_12 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Trace.resultAt
d_resultAt_508 ::
  () ->
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_T_110 -> MAlonzo.Code.Once.Res.T_Res_6
d_resultAt_508 ~v0 v1 v2 v3 = du_resultAt_508 v1 v2 v3
du_resultAt_508 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_T_110 -> MAlonzo.Code.Once.Res.T_Res_6
du_resultAt_508 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_run_342 (coe v0) (coe v1) (coe v2))
-- Once.Internal.Trace.valueT
d_valueT_526 ::
  () ->
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_T_110 -> AgdaAny -> AgdaAny
d_valueT_526 ~v0 v1 v2 v3 ~v4 = du_valueT_526 v1 v2 v3
du_valueT_526 ::
  T_Interp_182 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_T_110 -> AgdaAny
du_valueT_526 v0 v1 v2
  = coe
      du_resVal_502 (coe du_resultAt_508 (coe v0) (coe v1) (coe v2))
-- Once.Internal.Trace.RelT′
d_RelT'8242'_542 a0 a1 a2 a3 a4 = ()
data T_RelT'8242'_542
  = C_rel'45'ret_554 AgdaAny |
    C_rel'45'call_566 (AgdaAny -> T_RelT'8242'_542) | C_rel'45'halt_572
