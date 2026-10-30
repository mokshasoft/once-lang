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

module MAlonzo.Code.Once.SigOp.Info where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Arith.SigOp.BlockSem
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.SigOp.Info.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'base'45'to'45'full_422
      v2 v3 v4
-- Once.SigOp.Info.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.SigOp.Info.M.coerce-functor
d_coerce'45'functor_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.SigOp.Info.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.SigOp.Info.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.SigOp.Info.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'out_502 v2
      v3 v5
-- Once.SigOp.Info.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.SigOp.Info.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.SigOp.Info.M.eraseᵍ
d_erase'7501'_24 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.SigOp.Info.M.sem-CoIn
d_sem'45'CoIn_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_26 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.SigOp.Info.M.sem-CoOut
d_sem'45'CoOut_28 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_28 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoOut_636 v2 v3 v4
-- Once.SigOp.Info.M.sem-In
d_sem'45'In_30 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_30 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.SigOp.Info.M.sem-Out
d_sem'45'Out_32 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'Out_556 v2 v3 v4
-- Once.SigOp.Info.M.sem-ana
d_sem'45'ana_34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.SigOp.Info.M.sem-cata
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
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'cata_572 v2 v3 v5
-- Once.SigOp.Info.M.sem-fmap
d_sem'45'fmap_38 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.SigOp.Info.M.sem-para
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
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'para_592 v2 v3 v5 v6
-- Once.SigOp.Info.M.semAnaLayer
d_semAnaLayer_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.SigOp.Info.M.sfmapSemAna
d_sfmapSemAna_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sfmapSemAna_678 v0 v1 v2 v4
      v5
-- Once.SigOp.Info.M.⟦_⟧
d_'10214'_'10215'_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.SigOp.Info.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.SigOp.Info.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.SigOp.Info.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.SigOp.Info.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.SigOp.Info.EffectShape
d_EffectShape_58 a0 = ()
data T_EffectShape_58
  = C_Pure_62 | C_Emits_64 | C_Halts_66 | C_Answers_68
-- Once.SigOp.Info.SigOpSem
d_SigOpSem_74 a0 a1 = ()
data T_SigOpSem_74
  = C_blockV_86 MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8
                MAlonzo.Code.Once.Arith.Type.T_NumType_6
                MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 |
    C_ffiV_88 | C_callsV_90 | C_emitsV_92 | C_haltsV_94 |
    C_primV_96 MAlonzo.Code.Once.Arith.Prim.T_ArithPrim_208
-- Once.SigOp.Info.SigOpInfo
d_SigOpInfo_102 a0 a1 = ()
data T_SigOpInfo_102
  = C_mk'45'info''_124 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                       T_SigOpSem_74 MAlonzo.Code.Once.Spec.Type.T_Base_84
                       MAlonzo.Code.Once.Spec.Type.T_Base_84
-- Once.SigOp.Info.SigOpInfo.name
d_name_116 ::
  T_SigOpInfo_102 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_name_116 v0
  = case coe v0 of
      C_mk'45'info''_124 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.sem
d_sem_118 :: T_SigOpInfo_102 -> T_SigOpSem_74
d_sem_118 v0
  = case coe v0 of
      C_mk'45'info''_124 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.baseA
d_baseA_120 ::
  T_SigOpInfo_102 -> MAlonzo.Code.Once.Spec.Type.T_Base_84
d_baseA_120 v0
  = case coe v0 of
      C_mk'45'info''_124 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.SigOpInfo.conB
d_conB_122 ::
  T_SigOpInfo_102 -> MAlonzo.Code.Once.Spec.Type.T_Base_84
d_conB_122 v0
  = case coe v0 of
      C_mk'45'info''_124 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM-of
d_semM'45'of_130 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  T_SigOpSem_74 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_semM'45'of_130 v0 v1 v2 v3 v4
  = case coe v4 of
      C_blockV_86 v5 v6 v7
        -> coe
             (\ v10 v11 ->
                coe
                  MAlonzo.Code.Once.Res.C_returns_12
                  (coe
                     MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112
                     (coe
                        MAlonzo.Code.Once.Arith.Machine.IR.d_numtype'45'as'45'type_164
                        (coe v6))
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.BlockSem.d_block'45'semP_282 v5 v6 v7
                        v10 v11)))
      C_ffiV_88 -> coe (\ v5 -> coe v2 v3 v0 v1)
      C_callsV_90 -> coe (\ v5 -> coe v2 v3 v0 v1)
      C_emitsV_92
        -> coe
             (\ v6 v7 ->
                coe
                  MAlonzo.Code.Once.Res.C_returns_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      C_haltsV_94
        -> coe (\ v6 v7 -> coe MAlonzo.Code.Once.Res.C_stopped_10)
      C_primV_96 v5
        -> coe
             (\ v6 v7 ->
                coe
                  MAlonzo.Code.Once.Res.C_returns_12
                  (coe
                     MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 (coe v1)
                     (coe MAlonzo.Code.Once.Arith.Prim.du_primSem_238 v5 v6 v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.effect-of
d_effect'45'of_196 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_SigOpSem_74 -> T_EffectShape_58
d_effect'45'of_196 ~v0 ~v1 v2 = du_effect'45'of_196 v2
du_effect'45'of_196 :: T_SigOpSem_74 -> T_EffectShape_58
du_effect'45'of_196 v0
  = case coe v0 of
      C_blockV_86 v1 v2 v3 -> coe C_Pure_62
      C_ffiV_88 -> coe C_Pure_62
      C_callsV_90 -> coe C_Answers_68
      C_emitsV_92 -> coe C_Emits_64
      C_haltsV_94 -> coe C_Halts_66
      C_primV_96 v1 -> coe C_Pure_62
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.semM
d_semM_206 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  T_SigOpInfo_102 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_semM_206 v0 v1 v2 v3
  = coe
      d_semM'45'of_130 (coe v0) (coe v1) (coe v2)
      (coe d_name_116 (coe v3)) (coe d_sem_118 (coe v3))
-- Once.SigOp.Info.effect
d_effect_216 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_SigOpInfo_102 -> T_EffectShape_58
d_effect_216 ~v0 ~v1 v2 = du_effect_216 v2
du_effect_216 :: T_SigOpInfo_102 -> T_EffectShape_58
du_effect_216 v0 = coe du_effect'45'of_196 (coe d_sem_118 (coe v0))
-- Once.SigOp.Info.Internal
d_Internal_224 a0 a1 a2 = ()
data T_Internal_224 = C_int'45'block_240 | C_int'45'prim_244
-- Once.SigOp.Info.External
d_External_250 a0 a1 a2 = ()
data T_External_250
  = C_ext'45'ffi_256 | C_ext'45'calls_258 | C_ext'45'emits_262 |
    C_ext'45'halts_266
-- Once.SigOp.Info.sigop-owner
d_sigop'45'owner_274 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_SigOpSem_74 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sigop'45'owner_274 ~v0 ~v1 v2 = du_sigop'45'owner_274 v2
du_sigop'45'owner_274 ::
  T_SigOpSem_74 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sigop'45'owner_274 v0
  = case coe v0 of
      C_blockV_86 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe C_int'45'block_240)
      C_ffiV_88
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'ffi_256)
      C_callsV_90
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'calls_258)
      C_emitsV_92
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'emits_262)
      C_haltsV_94
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_ext'45'halts_266)
      C_primV_96 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe C_int'45'prim_244)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info.internal-pure
d_internal'45'pure_282 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_SigOpSem_74 ->
  T_Internal_224 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_internal'45'pure_282 = erased
-- Once.SigOp.Info.semP
d_semP_290 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_SigOpInfo_102 ->
  T_Internal_224 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
d_semP_290 ~v0 ~v1 v2 = du_semP_290 v2
du_semP_290 ::
  T_SigOpInfo_102 ->
  T_Internal_224 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
du_semP_290 v0 = coe du_semP'45'of_304 (coe d_sem_118 (coe v0))
-- Once.SigOp.Info._.semP-of
d_semP'45'of_304 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_SigOpInfo_102 ->
  T_SigOpSem_74 ->
  T_Internal_224 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
d_semP'45'of_304 ~v0 ~v1 ~v2 v3 v4 = du_semP'45'of_304 v3 v4
du_semP'45'of_304 ::
  T_SigOpSem_74 ->
  T_Internal_224 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> AgdaAny -> AgdaAny
du_semP'45'of_304 v0 v1
  = case coe v0 of
      C_blockV_86 v2 v3 v4
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.BlockSem.d_block'45'semP_282 (coe v2)
                (coe v3) (coe v4))
      C_ffiV_88 -> coe (\ v2 v3 -> MAlonzo.RTE.mazUnreachableError)
      C_callsV_90 -> coe (\ v2 v3 -> MAlonzo.RTE.mazUnreachableError)
      C_emitsV_92 -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      C_haltsV_94 -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      C_primV_96 v2
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Once.Arith.Prim.du_primSem_238 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.SigOp.Info._≟SigOpInfo-name_
d__'8799'SigOpInfo'45'name__318 ::
  T_SigOpInfo_102 ->
  T_SigOpInfo_102 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'SigOpInfo'45'name__318 v0 v1
  = coe
      MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
      (coe d_name_116 (coe v0)) (coe d_name_116 (coe v1))
