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

module MAlonzo.Code.Once.LinCore.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Float.Word
import qualified MAlonzo.Code.Once.IR.Semantics.Iterative
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word

-- Val.coerce-base-to-full
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
-- Val.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Val.coerce-functor
d_coerce'45'functor_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Val.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Val.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Val.coerce-μ-out
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
-- Val.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Val.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Val.eraseᵍ
d_erase'7501'_24 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Val.sem-CoIn
d_sem'45'CoIn_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_26 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Val.sem-CoOut
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
-- Val.sem-In
d_sem'45'In_30 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_30 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Val.sem-Out
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
-- Val.sem-ana
d_sem'45'ana_34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Val.sem-cata
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
-- Val.sem-fmap
d_sem'45'fmap_38 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Val.sem-para
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
-- Val.semAnaLayer
d_semAnaLayer_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Val.sfmapSemAna
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
-- Val.⟦_⟧
d_'10214'_'10215'_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_46 = erased
-- Val.⟦_⟧F
d_'10214'_'10215'F_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Val.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Val.⟦μ⟧
d_'10214'μ'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_52 = erased
-- Val.⟦ν⟧
d_'10214'ν'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.LinCore.Core.lit
d_lit_60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> AgdaAny -> AgdaAny
d_lit_60 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Flat.C_int_48
        -> coe
             MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
             (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
             (coe v2)
      MAlonzo.Code.Once.LinCore.Flat.C_float_50
        -> coe
             MAlonzo.Code.Once.Float.Word.d_round_58
             (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.block
d_block_68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_10 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_block_68 ~v0 ~v1 v2 = du_block_68 v2
du_block_68 ::
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_10 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_block_68 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Iterative.d_force_16 (coe v0)
-- Once.LinCore.Core.⟦_⟧f
d_'10214'_'10215'f_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> ()
d_'10214'_'10215'f_70 = erased
-- Once.LinCore.Core.bindT
d_bindT_76 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_bindT_76 ~v0 ~v1 ~v2 v3 v4 = du_bindT_76 v3 v4
du_bindT_76 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_bindT_76 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2 -> coe v1 v2
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_bindT_76 (coe v4 v5) (coe v1)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.fmapT
d_fmapT_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_fmapT_102 ~v0 ~v1 ~v2 v3 v4 = du_fmapT_102 v3 v4
du_fmapT_102 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_fmapT_102 v0 v1
  = coe
      du_bindT_76 (coe v1)
      (coe
         (\ v2 ->
            coe MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 (coe v0 v2)))
-- Once.LinCore.Core.embB
d_embB_112 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_embB_112 ~v0 ~v1 v2 = du_embB_112 v2
du_embB_112 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_embB_112 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v1
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v1) (coe v2)
             (coe (\ v4 -> coe du_embB_112 (coe v3 v4)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.emb
d_emb_130 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_10
d_emb_130 ~v0 ~v1 v2 = du_emb_130 v2
du_emb_130 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_10
du_emb_130 v0
  = coe
      MAlonzo.Code.Once.IR.Semantics.Iterative.C_constructor_18
      (coe du_embB_112 (coe v0))
-- Once.LinCore.Core.LF
d_LF_134 a0 = ()
data T_LF_134
  = C_Idf_136 | C_Kone_138 | C_Kzero_140 |
    C_Kb_142 MAlonzo.Code.Once.LinCore.Flat.T_Base_46 |
    C_Kμ_144 T_LF_134 | C__'8853'f__146 T_LF_134 T_LF_134 |
    C__'8855'f__148 T_LF_134 T_LF_134
-- Once.LinCore.Core.Kd
d_Kd_150 a0 = ()
data T_Kd_150 = C_once_152 | C_many_154
-- Once.LinCore.Core.Gr
d_Gr_156 a0 = ()
data T_Gr_156 = C_act_158 | C_eff_160
-- Once.LinCore.Core.Mg
d_Mg_162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Gr_156 -> () -> ()
d_Mg_162 = erased
-- Once.LinCore.Core.up
d_up_172 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Gr_156 ->
  () ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_10
d_up_172 ~v0 v1 ~v2 v3 = du_up_172 v1 v3
du_up_172 ::
  T_Gr_156 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_10
du_up_172 v0 v1
  = case coe v0 of
      C_act_158 -> coe du_emb_130 (coe v1)
      C_eff_160 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.LTy
d_LTy_178 a0 = ()
data T_LTy_178
  = C_One_180 | C_Zero_182 | C__'8855't__184 T_LTy_178 T_LTy_178 |
    C__'8853't__186 T_LTy_178 T_LTy_178 | C_Ct_188 Integer T_LTy_178 |
    C_Fn_190 T_Kd_150 T_Gr_156 T_LTy_178 T_LTy_178 |
    C_Nu_192 T_LF_134 | C_μt_194 T_LF_134 |
    C_Bt_196 MAlonzo.Code.Once.LinCore.Flat.T_Base_46
-- Once.LinCore.Core.LF∙
d_LF'8729'_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 -> T_LTy_178 -> T_LTy_178
d_LF'8729'_198 ~v0 v1 v2 = du_LF'8729'_198 v1 v2
du_LF'8729'_198 :: T_LF_134 -> T_LTy_178 -> T_LTy_178
du_LF'8729'_198 v0 v1
  = case coe v0 of
      C_Idf_136 -> coe v1
      C_Kone_138 -> coe C_One_180
      C_Kzero_140 -> coe C_Zero_182
      C_Kb_142 v2 -> coe C_Bt_196 (coe v2)
      C_Kμ_144 v2 -> coe C_μt_194 (coe v2)
      C__'8853'f__146 v2 v3
        -> coe
             C__'8853't__186 (coe du_LF'8729'_198 (coe v2) (coe v1))
             (coe du_LF'8729'_198 (coe v3) (coe v1))
      C__'8855'f__148 v2 v3
        -> coe
             C__'8855't__184 (coe du_LF'8729'_198 (coe v2) (coe v1))
             (coe du_LF'8729'_198 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.FS
d_FS_226 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 -> () -> ()
d_FS_226 = erased
-- Once.LinCore.Core.Mu
d_Mu_230 a0 a1 = ()
newtype T_Mu_230 = C_inμ_260 AgdaAny
-- Once.LinCore.Core.outμ
d_outμ_264 :: T_Mu_230 -> AgdaAny
d_outμ_264 v0
  = case coe v0 of
      C_inμ_260 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Nuᵐ
d_Nu'7504'_270 a0 a1 = ()
data T_Nu'7504'_270
  = C_constructor_278 MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
-- Once.LinCore.Core.Nuᵐ.outν
d_outν_276 ::
  T_Nu'7504'_270 -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_outν_276 v0
  = case coe v0 of
      C_constructor_278 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.anaN
d_anaN_284 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_Nu'7504'_270
d_anaN_284 v0 v1 ~v2 v3 v4 = du_anaN_284 v0 v1 v3 v4
du_anaN_284 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_Nu'7504'_270
du_anaN_284 v0 v1 v2 v3
  = coe
      C_constructor_278
      (coe du_treeN_290 (coe v0) (coe v1) (coe v2) (coe v2 v3))
-- Once.LinCore.Core.treeN
d_treeN_290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_treeN_290 v0 v1 ~v2 v3 v4 = du_treeN_290 v0 v1 v3 v4
du_treeN_290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_treeN_290 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
             (coe du_mapN_298 (coe v0) (coe v1) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v4) (coe v5)
             (coe
                (\ v7 -> coe du_treeN_290 (coe v0) (coe v1) (coe v2) (coe v6 v7)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.mapN
d_mapN_298 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  T_LF_134 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> AgdaAny
d_mapN_298 v0 v1 v2 ~v3 v4 v5 = du_mapN_298 v0 v1 v2 v4 v5
du_mapN_298 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  T_LF_134 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> AgdaAny
du_mapN_298 v0 v1 v2 v3 v4
  = case coe v2 of
      C_Idf_136 -> coe du_anaN_284 (coe v0) (coe v1) (coe v3) (coe v4)
      C_Kone_138 -> coe v4
      C_Kb_142 v5 -> coe v4
      C_Kμ_144 v5 -> coe v4
      C__'8853'f__146 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapN_298 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapN_298 (coe v0) (coe v1) (coe v6) (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'f__148 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapN_298 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
                    (coe du_mapN_298 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.⟦_⟧
d_'10214'_'10215'_396 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_LTy_178 -> ()
d_'10214'_'10215'_396 = erased
-- Once.LinCore.Core.coh
d_coh_428 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 -> T_LTy_178 -> AgdaAny -> AgdaAny
d_coh_428 ~v0 v1 ~v2 v3 = du_coh_428 v1 v3
du_coh_428 :: T_LF_134 -> AgdaAny -> AgdaAny
du_coh_428 v0 v1
  = case coe v0 of
      C_Idf_136 -> coe v1
      C_Kone_138 -> coe v1
      C_Kb_142 v2 -> coe v1
      C_Kμ_144 v2 -> coe v1
      C__'8853'f__146 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coh_428 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coh_428 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'f__148 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coh_428 (coe v2) (coe v4))
                    (coe du_coh_428 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.coh⁻¹
d_coh'8315''185'_482 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 -> T_LTy_178 -> AgdaAny -> AgdaAny
d_coh'8315''185'_482 ~v0 v1 ~v2 v3 = du_coh'8315''185'_482 v1 v3
du_coh'8315''185'_482 :: T_LF_134 -> AgdaAny -> AgdaAny
du_coh'8315''185'_482 v0 v1
  = case coe v0 of
      C_Idf_136 -> coe v1
      C_Kone_138 -> coe v1
      C_Kb_142 v2 -> coe v1
      C_Kμ_144 v2 -> coe v1
      C__'8853'f__146 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coh'8315''185'_482 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coh'8315''185'_482 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'f__148 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coh'8315''185'_482 (coe v2) (coe v4))
                    (coe du_coh'8315''185'_482 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.⌜_⌝
d_'8988'_'8989'_532 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> T_LTy_178
d_'8988'_'8989'_532 ~v0 v1 = du_'8988'_'8989'_532 v1
du_'8988'_'8989'_532 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> T_LTy_178
du_'8988'_'8989'_532 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe C_One_180
      MAlonzo.Code.Once.LinCore.Flat.C_fvoid_14 -> coe C_Zero_182
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v1 -> coe C_Bt_196 (coe v1)
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v1 v2
        -> coe
             C__'8855't__184 (coe du_'8988'_'8989'_532 (coe v1))
             (coe du_'8988'_'8989'_532 (coe v2))
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v1 v2
        -> coe
             C__'8853't__186 (coe du_'8988'_'8989'_532 (coe v1))
             (coe du_'8988'_'8989'_532 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.toF
d_toF_546 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
d_toF_546 ~v0 v1 v2 = du_toF_546 v1 v2
du_toF_546 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
du_toF_546 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_toF_546 (coe v2) (coe v4))
                    (coe du_toF_546 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_toF_546 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_toF_546 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.fromF
d_fromF_576 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
d_fromF_576 ~v0 v1 v2 = du_fromF_576 v1 v2
du_fromF_576 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
du_fromF_576 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_fromF_576 (coe v2) (coe v4))
                    (coe du_fromF_576 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_fromF_576 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_fromF_576 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.flat
d_flat_606 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_flat_606 ~v0 v1 v2 = du_flat_606 v1 v2
du_flat_606 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_flat_606 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94
        -> coe MAlonzo.Code.Once.LinCore.Flat.C_funit_12
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe MAlonzo.Code.Once.LinCore.Flat.C_fvoid_14
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98
        -> coe
             MAlonzo.Code.Once.LinCore.Flat.C_fw_16
             (coe MAlonzo.Code.Once.LinCore.Flat.C_int_48)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100
        -> coe
             MAlonzo.Code.Once.LinCore.Flat.C_fw_16
             (coe MAlonzo.Code.Once.LinCore.Flat.C_float_50)
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18
                    (coe du_flat_606 (coe v6) (coe v4))
                    (coe du_flat_606 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20
                    (coe du_flat_606 (coe v6) (coe v4))
                    (coe du_flat_606 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.toV
d_toV_620 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_toV_620 ~v0 v1 v2 = du_toV_620 v1 v2
du_toV_620 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
du_toV_620 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94 -> coe (\ v2 -> v2)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98 -> coe (\ v2 -> v2)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100 -> coe (\ v2 -> v2)
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    (\ v8 ->
                       case coe v8 of
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                           -> coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe du_toV_620 v6 v4 v9) (coe du_toV_620 v7 v5 v10)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    (\ v8 ->
                       case coe v8 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                           -> coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe du_toV_620 v6 v4 v9)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                           -> coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe du_toV_620 v7 v5 v9)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.fromV
d_fromV_652 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_fromV_652 ~v0 v1 v2 = du_fromV_652 v1 v2
du_fromV_652 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
du_fromV_652 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94 -> coe (\ v2 -> v2)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96
        -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Int_98 -> coe (\ v2 -> v2)
      MAlonzo.Code.Once.Spec.Type.C_b'45'Float_100 -> coe (\ v2 -> v2)
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v6 v7
               -> coe
                    (\ v8 ->
                       case coe v8 of
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                           -> coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe du_fromV_652 v6 v4 v9) (coe du_fromV_652 v7 v5 v10)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    (\ v8 ->
                       case coe v8 of
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                           -> coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                (coe du_fromV_652 v6 v4 v9)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                           -> coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                (coe du_fromV_652 v7 v5 v9)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sig
d_Sig_680 a0 = ()
data T_Sig_680
  = C_sig_694 MAlonzo.Code.Once.Spec.Type.T_Ty_8
              MAlonzo.Code.Once.Spec.Type.T_Ty_8
              MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
-- Once.LinCore.Core.Sig.sA
d_sA_688 :: T_Sig_680 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_688 v0
  = case coe v0 of
      C_sig_694 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sig.sB
d_sB_690 :: T_Sig_680 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_690 v0
  = case coe v0 of
      C_sig_694 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sig.info
d_info_692 ::
  T_Sig_680 -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_692 v0
  = case coe v0 of
      C_sig_694 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.sdom
d_sdom_696 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Sig_680 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_696 ~v0 v1 = du_sdom_696 v1
du_sdom_696 :: T_Sig_680 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_696 v0
  = coe
      du_flat_606 (coe d_sA_688 (coe v0))
      (coe
         MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe d_info_692 (coe v0)))
-- Once.LinCore.Core.scod
d_scod_698 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Sig_680 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_698 ~v0 v1 = du_scod_698 v1
du_scod_698 :: T_Sig_680 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_698 v0
  = coe
      du_flat_606 (coe d_sB_690 (coe v0))
      (coe
         MAlonzo.Code.Once.SigOp.Info.d_conB_122 (coe d_info_692 (coe v0)))
-- Once.LinCore.Core.Sg
d_Sg_704 a0 = ()
data T_Sg_704
  = C_sg_726 T_Kd_150 T_Gr_156 T_LTy_178 T_LTy_178 T_LTy_178
-- Once.LinCore.Core.Sg.kd
d_kd_716 :: T_Sg_704 -> T_Kd_150
d_kd_716 v0
  = case coe v0 of
      C_sg_726 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.gr
d_gr_718 :: T_Sg_704 -> T_Gr_156
d_gr_718 v0
  = case coe v0 of
      C_sg_726 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.env
d_env_720 :: T_Sg_704 -> T_LTy_178
d_env_720 v0
  = case coe v0 of
      C_sg_726 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.dom
d_dom_722 :: T_Sg_704 -> T_LTy_178
d_dom_722 v0
  = case coe v0 of
      C_sg_726 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.cod
d_cod_724 :: T_Sg_704 -> T_LTy_178
d_cod_724 v0
  = case coe v0 of
      C_sg_726 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Cx
d_Cx_728 a0 = ()
data T_Cx_728 = C_ε_730 | C__'9656'__732 T_Cx_728 T_Sg_704
-- Once.LinCore.Core.len
d_len_734 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 -> Integer
d_len_734 ~v0 v1 = du_len_734 v1
du_len_734 :: T_Cx_728 -> Integer
du_len_734 v0
  = case coe v0 of
      C_ε_730 -> coe (0 :: Integer)
      C__'9656'__732 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_len_734 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core._∋[_]_
d__'8715''91'_'93'__738 a0 a1 a2 a3 = ()
data T__'8715''91'_'93'__738
  = C_here_744 | C_there_754 T__'8715''91'_'93'__738
-- Once.LinCore.Core.Tm
d_Tm_758 a0 a1 a2 a3 a4 = ()
data T_Tm_758
  = C_lid_786 | C__'8728'l__796 T_LTy_178 T_Tm_758 T_Tm_758 |
    C__'8855'l__808 T_Tm_758 T_Tm_758 | C_ρl_814 | C_ρl'8315'_820 |
    C_lul_826 | C_lul'8315'_832 | C_lassoc_842 | C_lassoc'8315'_852 |
    C_lswap_860 | C_dup_866 | C_drop_872 | C_linl_880 | C_linr_888 |
    C_lcase_898 T_Tm_758 T_Tm_758 | C_lzero_904 | C_lIn_910 |
    C_lOutμ_916 | C_lcata_924 T_Tm_758 |
    C_lclo_942 T_LF_134 Integer T_Kd_150 T_Gr_156 T_LTy_178 T_LTy_178
               T_LTy_178 T__'8715''91'_'93'__738 |
    C_lapp_956 T_Gr_156 T__'8715''91'_'93'__738 | C_lend_966 T_Tm_758 |
    C_blift_974 T_Tm_758 | C_bfst_984 T_Tm_758 | C_bsnd_994 T_Tm_758 |
    C_bcaseE_1004 T_Tm_758 T_Tm_758 | C_bout_1012 T_Tm_758 |
    C_bcopy_1016 | C_bapp_1028 T_Gr_156 T__'8715''91'_'93'__738 |
    C_llam_1042 T_Tm_758 AgdaAny | C_llamω_1056 T_Tm_758 AgdaAny |
    C_lev_1066 | C_bev_1074 | C_llamω'7580'_1088 T_Tm_758 AgdaAny |
    C_levω_1098 | C_lunf_1106 | C_lout_1112 | C_lconst_1118 AgdaAny |
    C_lop_1124 T_Sig_680 | C_liter_1134 T_Tm_758 T_Blk_768
-- Once.LinCore.Core.Blk
d_Blk_768 a0 a1 a2 a3 a4 a5 = ()
data T_Blk_768
  = C_k'45'id_1142 | C_k'45''8728'_1156 T_Blk_768 T_Blk_768 |
    C_k'45''8855'_1172 T_Blk_768 T_Blk_768 | C_k'45'ρ_1178 |
    C_k'45'ρ'8315'_1184 | C_k'45'lul_1190 | C_k'45'lul'8315'_1196 |
    C_k'45'assoc_1206 | C_k'45'assoc'8315'_1216 | C_k'45'swap_1224 |
    C_k'45'dup_1230 | C_k'45'drop_1236 | C_k'45'inl_1244 |
    C_k'45'inr_1252 | C_k'45'case_1266 T_Blk_768 T_Blk_768 |
    C_k'45'zero_1272 | C_k'45'in_1278 | C_k'45'out_1284 |
    C_k'45'cata_1294 T_Blk_768 | C_k'45'clo_1314 | C_k'45'app_1328 |
    C_k'45'lend_1340 T_Blk_768 | C_k'45'lift_1350 T_Blk_768 |
    C_k'45'fst_1362 T_Blk_768 | C_k'45'snd_1374 T_Blk_768 |
    C_k'45'caseE_1388 T_Blk_768 T_Blk_768 |
    C_k'45'bout_1398 T_Blk_768 | C_k'45'copy_1402 | C_k'45'bapp_1414 |
    C_k'45'lam_1430 | C_k'45'lamω_1446 | C_k'45'ev_1454 |
    C_k'45'bev_1460 | C_k'45'lamω'7580'_1476 | C_k'45'evω_1484 |
    C_k'45'unf_1492 | C_k'45'nout_1498 | C_k'45'const_1506 |
    C_k'45'op_1512
-- Once.LinCore.Core.Gd
d_Gd_778 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 ->
  T_LTy_178 -> T_LTy_178 -> T_LTy_178 -> T_Gr_156 -> T_Tm_758 -> ()
d_Gd_778 = erased
-- Once.LinCore.Core.LTm
d_LTm_1514 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 -> T_LTy_178 -> T_LTy_178 -> ()
d_LTm_1514 = erased
-- Once.LinCore.Core.Coalg
d_Coalg_1518 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 -> T_LTy_178 -> T_LTy_178
d_Coalg_1518 ~v0 v1 v2 = du_Coalg_1518 v1 v2
du_Coalg_1518 :: T_LF_134 -> T_LTy_178 -> T_LTy_178
du_Coalg_1518 v0 v1
  = coe
      C_Fn_190 (coe C_many_154) (coe C_act_158) (coe v1)
      (coe du_LF'8729'_198 (coe v0) (coe v1))
-- Once.LinCore.Core.strL
d_strL_1532 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 -> T_LF_134 -> T_LF_134 -> T_LTy_178 -> T_Tm_758
d_strL_1532 ~v0 ~v1 v2 v3 v4 = du_strL_1532 v2 v3 v4
du_strL_1532 :: T_LF_134 -> T_LF_134 -> T_LTy_178 -> T_Tm_758
du_strL_1532 v0 v1 v2
  = case coe v1 of
      C_Idf_136
        -> coe
             C__'8728'l__796 (coe C__'8855't__184 (coe C_One_180) (coe v2))
             (coe
                C__'8855'l__808 (coe C_bsnd_994 (coe C_bcopy_1016))
                (coe C_lid_786))
             (coe C_lul'8315'_832)
      C_Kone_138 -> coe C_lid_786
      C_Kzero_140 -> coe C_lid_786
      C_Kb_142 v3 -> coe C_lid_786
      C_Kμ_144 v3 -> coe C_lid_786
      C__'8853'f__146 v3 v4
        -> coe
             C_lcase_898
             (coe
                C__'8728'l__796
                (coe
                   du_LF'8729'_198 (coe v3)
                   (coe
                      C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v2)) (coe v2)))
                (coe C_linl_880) (coe du_strL_1532 (coe v0) (coe v3) (coe v2)))
             (coe
                C__'8728'l__796
                (coe
                   du_LF'8729'_198 (coe v4)
                   (coe
                      C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v2)) (coe v2)))
                (coe C_linr_888) (coe du_strL_1532 (coe v0) (coe v4) (coe v2)))
      C__'8855'f__148 v3 v4
        -> coe
             C__'8855'l__808 (coe du_strL_1532 (coe v0) (coe v3) (coe v2))
             (coe du_strL_1532 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.mapNu
d_mapNu_1582 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 -> T_LF_134 -> T_LF_134 -> T_LTy_178 -> T_Tm_758
d_mapNu_1582 ~v0 ~v1 v2 v3 ~v4 = du_mapNu_1582 v2 v3
du_mapNu_1582 :: T_LF_134 -> T_LF_134 -> T_Tm_758
du_mapNu_1582 v0 v1
  = case coe v1 of
      C_Idf_136 -> coe C_lunf_1106
      C_Kone_138 -> coe C_lid_786
      C_Kzero_140 -> coe C_lid_786
      C_Kb_142 v2 -> coe C_lid_786
      C_Kμ_144 v2 -> coe C_lid_786
      C__'8853'f__146 v2 v3
        -> coe
             C_lcase_898
             (coe
                C__'8728'l__796
                (coe du_LF'8729'_198 (coe v2) (coe C_Nu_192 (coe v0)))
                (coe C_linl_880) (coe du_mapNu_1582 (coe v0) (coe v2)))
             (coe
                C__'8728'l__796
                (coe du_LF'8729'_198 (coe v3) (coe C_Nu_192 (coe v0)))
                (coe C_linr_888) (coe du_mapNu_1582 (coe v0) (coe v3)))
      C__'8855'f__148 v2 v3
        -> coe
             C__'8855'l__808 (coe du_mapNu_1582 (coe v0) (coe v2))
             (coe du_mapNu_1582 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.obsT
d_obsT_1630 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 -> T_LF_134 -> T_LTy_178 -> T_Tm_758
d_obsT_1630 ~v0 ~v1 v2 v3 = du_obsT_1630 v2 v3
du_obsT_1630 :: T_LF_134 -> T_LTy_178 -> T_Tm_758
du_obsT_1630 v0 v1
  = coe
      C__'8728'l__796
      (coe
         du_LF'8729'_198 (coe v0)
         (coe
            C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v1)) (coe v1)))
      (coe du_mapNu_1582 (coe v0) (coe v0))
      (coe
         C__'8728'l__796
         (coe
            C__'8855't__184 (coe C_One_180)
            (coe
               du_LF'8729'_198 (coe v0)
               (coe
                  C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v1)) (coe v1))))
         (coe C_lul_826)
         (coe
            C__'8728'l__796
            (coe
               C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v1))
               (coe
                  du_LF'8729'_198 (coe v0)
                  (coe
                     C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v1)) (coe v1))))
            (coe C__'8855'l__808 (coe C_drop_872) (coe C_lid_786))
            (coe
               C__'8728'l__796
               (coe
                  C__'8855't__184 (coe du_Coalg_1518 (coe v0) (coe v1))
                  (coe du_LF'8729'_198 (coe v0) (coe v1)))
               (coe C_lend_966 (coe du_strL_1532 (coe v0) (coe v0) (coe v1)))
               (coe C_lend_966 (coe C_bsnd_994 (coe C_bev_1074))))))
-- Once.LinCore.Core.cohc
d_cohc_1640 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  T_LTy_178 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_cohc_1640 ~v0 v1 ~v2 v3 v4 = du_cohc_1640 v1 v3 v4
du_cohc_1640 ::
  T_LF_134 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_cohc_1640 v0 v1 v2
  = coe du_fmapT_102 (coe du_coh_428 (coe v0)) (coe v1 v2)
-- Once.LinCore.Core.lana
d_lana_1660 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 ->
  Integer ->
  T_LTy_178 ->
  T_LTy_178 -> T_LTy_178 -> T__'8715''91'_'93'__738 -> T_Tm_758
d_lana_1660 ~v0 ~v1 v2 v3 v4 ~v5 v6 = du_lana_1660 v2 v3 v4 v6
du_lana_1660 ::
  Integer ->
  T_LTy_178 -> T_LTy_178 -> T__'8715''91'_'93'__738 -> T_Tm_758
du_lana_1660 v0 v1 v2 v3
  = coe
      C_lclo_942 (coe C_Idf_136) v0 (coe C_once_152) (coe C_act_158) v1
      (coe C_One_180) v2 v3
-- Once.LinCore.Core.lobs
d_lobs_1674 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  T_Cx_728 ->
  Integer ->
  T_LTy_178 -> T_LTy_178 -> T__'8715''91'_'93'__738 -> T_Tm_758
d_lobs_1674 ~v0 v1 ~v2 v3 v4 ~v5 v6 = du_lobs_1674 v1 v3 v4 v6
du_lobs_1674 ::
  T_LF_134 ->
  Integer -> T_LTy_178 -> T__'8715''91'_'93'__738 -> T_Tm_758
du_lobs_1674 v0 v1 v2 v3
  = coe
      C__'8728'l__796 (coe du_LF'8729'_198 (coe v0) (coe v2))
      (coe
         C_lclo_942 v0 v1 (coe C_once_152) (coe C_act_158) v2
         (coe C_One_180) (coe du_LF'8729'_198 (coe v0) (coe v2)) v3)
      (coe
         C__'8728'l__796
         (coe
            C__'8855't__184 (coe C_Ct_188 (coe v1) (coe v2)) (coe C_One_180))
         (coe C_lapp_956 (coe C_act_158) v3) (coe C_ρl'8315'_820))
-- Once.LinCore.Core.k-obs
d_k'45'obs_1692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_134 ->
  T_Cx_728 ->
  Integer ->
  T_LTy_178 -> T_LTy_178 -> T__'8715''91'_'93'__738 -> T_Blk_768
d_k'45'obs_1692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_k'45'obs_1692
du_k'45'obs_1692 :: T_Blk_768
du_k'45'obs_1692
  = coe
      C_k'45''8728'_1156 (coe C_k'45'clo_1314)
      (coe
         C_k'45''8728'_1156 (coe C_k'45'app_1328) (coe C_k'45'ρ'8315'_1184))
-- Once.LinCore.Core.cin
d_cin_1708 ::
  T_Cx_728 ->
  T_LTy_178 -> T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> T_Tm_758
d_cin_1708 ~v0 v1 v2 ~v3 v4 = du_cin_1708 v1 v2 v4
du_cin_1708 :: T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> T_Tm_758
du_cin_1708 v0 v1 v2
  = coe
      C__'8728'l__796 (coe C__'8855't__184 (coe v0) (coe v1))
      (coe C_blift_974 v2)
      (coe
         C__'8728'l__796 (coe C__'8855't__184 (coe C_One_180) (coe v1))
         (coe C__'8855'l__808 (coe C_bcopy_1016) (coe C_lid_786))
         (coe C_lul'8315'_832))
-- Once.LinCore.Core.k-cin
d_k'45'cin_1722 ::
  T_Cx_728 ->
  T_LTy_178 ->
  T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> T_Blk_768 -> T_Blk_768
d_k'45'cin_1722 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'cin_1722 v5
du_k'45'cin_1722 :: T_Blk_768 -> T_Blk_768
du_k'45'cin_1722 v0
  = coe
      C_k'45''8728'_1156 (coe C_k'45'lift_1350 v0)
      (coe
         C_k'45''8728'_1156
         (coe
            C_k'45''8855'_1172 (coe C_k'45'copy_1402) (coe C_k'45'id_1142))
         (coe C_k'45'lul'8315'_1196))
-- Once.LinCore.Core.ownBg
d_ownBg_1734 ::
  T_Cx_728 ->
  T_LTy_178 -> T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> T_Tm_758
d_ownBg_1734 ~v0 v1 ~v2 v3 v4 = du_ownBg_1734 v1 v3 v4
du_ownBg_1734 :: T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> T_Tm_758
du_ownBg_1734 v0 v1 v2
  = coe
      C__'8728'l__796 (coe C__'8855't__184 (coe v0) (coe v1))
      (coe
         C__'8728'l__796 (coe C__'8855't__184 (coe C_One_180) (coe v1))
         (coe C_lul_826)
         (coe C__'8855'l__808 (coe C_drop_872) (coe C_lid_786)))
      (coe C_lend_966 (coe C_bsnd_994 v2))
-- Once.LinCore.Core.ownBg-gd
d_ownBg'45'gd_1750 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 ->
  T_Gr_156 ->
  T_LTy_178 ->
  T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> AgdaAny -> AgdaAny
d_ownBg'45'gd_1750 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_ownBg'45'gd_1750 v2 v7
du_ownBg'45'gd_1750 :: T_Gr_156 -> AgdaAny -> AgdaAny
du_ownBg'45'gd_1750 v0 v1
  = case coe v0 of
      C_act_158
        -> coe
             C_k'45''8728'_1156
             (coe
                C_k'45''8728'_1156 (coe C_k'45'lul_1190)
                (coe
                   C_k'45''8855'_1172 (coe C_k'45'drop_1236) (coe C_k'45'id_1142)))
             (coe C_k'45'lend_1340 (coe C_k'45'snd_1374 v1))
      C_eff_160 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.cin-gd
d_cin'45'gd_1772 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 ->
  T_Gr_156 ->
  T_LTy_178 ->
  T_LTy_178 -> T_LTy_178 -> T_Tm_758 -> AgdaAny -> AgdaAny
d_cin'45'gd_1772 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_cin'45'gd_1772 v2 v7
du_cin'45'gd_1772 :: T_Gr_156 -> AgdaAny -> AgdaAny
du_cin'45'gd_1772 v0 v1
  = case coe v0 of
      C_act_158
        -> coe
             C_k'45''8728'_1156 (coe C_k'45'lift_1350 v1)
             (coe
                C_k'45''8728'_1156
                (coe
                   C_k'45''8855'_1172 (coe C_k'45'copy_1402) (coe C_k'45'id_1142))
                (coe C_k'45'lul'8315'_1196))
      C_eff_160 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Body
d_Body_1784 a0 a1 a2 = ()
data T_Body_1784
  = C_b1_1798 T_Tm_758 AgdaAny | C_bω_1810 T_Tm_758 AgdaAny
-- Once.LinCore.Core.Defs
d_Defs_1812 a0 a1 = ()
data T_Defs_1812
  = C_ε_1814 | C__'9656'__1820 T_Defs_1812 T_Body_1784
-- Once.LinCore.Core.Look
d_Look_1830 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Look_1830
  = C_lk'45'here_1840 | C_lk'45'there_1862 T_Look_1830
-- Once.LinCore.Core.Env
d_Env_1864 a0 a1 = ()
data T_Env_1864
  = C_ε_1866 |
    C__'9656'__1872 T_Env_1864 (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.LinCore.Core.lookup
d_lookup_1880 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_728 ->
  Integer ->
  T_Sg_704 ->
  T_Env_1864 ->
  T__'8715''91'_'93'__738 -> AgdaAny -> AgdaAny -> AgdaAny
d_lookup_1880 ~v0 v1 ~v2 ~v3 v4 v5 = du_lookup_1880 v1 v4 v5
du_lookup_1880 ::
  T_Cx_728 ->
  T_Env_1864 ->
  T__'8715''91'_'93'__738 -> AgdaAny -> AgdaAny -> AgdaAny
du_lookup_1880 v0 v1 v2
  = case coe v1 of
      C_ε_1866 -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      C__'9656'__1872 v5 v6
        -> case coe v0 of
             C__'9656'__732 v7 v8
               -> case coe v2 of
                    C_here_744 -> coe v6
                    C_there_754 v13 -> coe du_lookup_1880 (coe v7) (coe v5) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
