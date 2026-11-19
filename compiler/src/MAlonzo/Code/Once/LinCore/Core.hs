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
-- Once.LinCore.Core.⟦_⟧f
d_'10214'_'10215'f_66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> ()
d_'10214'_'10215'f_66 = erased
-- Once.LinCore.Core.bindT
d_bindT_72 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_bindT_72 ~v0 ~v1 ~v2 v3 v4 = du_bindT_72 v3 v4
du_bindT_72 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_bindT_72 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2 -> coe v1 v2
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_bindT_72 (coe v4 v5) (coe v1)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.fmapT
d_fmapT_98 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_fmapT_98 ~v0 ~v1 ~v2 v3 v4 = du_fmapT_98 v3 v4
du_fmapT_98 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_fmapT_98 v0 v1
  = coe
      du_bindT_72 (coe v1)
      (coe
         (\ v2 ->
            coe MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 (coe v0 v2)))
-- Once.LinCore.Core.embB
d_embB_108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_embB_108 ~v0 ~v1 v2 = du_embB_108 v2
du_embB_108 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_embB_108 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v1
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v1) (coe v2)
             (coe (\ v4 -> coe du_embB_108 (coe v3 v4)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.emb
d_emb_126 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
d_emb_126 ~v0 ~v1 v2 = du_emb_126 v2
du_emb_126 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
du_emb_126 v0
  = coe
      MAlonzo.Code.Once.IR.Semantics.Iterative.C_constructor_68
      (coe du_embB_108 (coe v0))
-- Once.LinCore.Core.LF
d_LF_130 a0 = ()
data T_LF_130
  = C_Idf_132 | C_Kone_134 | C_Kzero_136 |
    C_Kb_138 MAlonzo.Code.Once.LinCore.Flat.T_Base_46 |
    C_Kμ_140 T_LF_130 | C__'8853'f__142 T_LF_130 T_LF_130 |
    C__'8855'f__144 T_LF_130 T_LF_130
-- Once.LinCore.Core.Kd
d_Kd_146 a0 = ()
data T_Kd_146 = C_once_148 | C_many_150
-- Once.LinCore.Core.Gr
d_Gr_152 a0 = ()
data T_Gr_152 = C_act_154 | C_eff_156
-- Once.LinCore.Core.Mg
d_Mg_158 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Gr_152 -> () -> ()
d_Mg_158 = erased
-- Once.LinCore.Core.up
d_up_168 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Gr_152 ->
  () ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
d_up_168 ~v0 v1 ~v2 v3 = du_up_168 v1 v3
du_up_168 ::
  T_Gr_152 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
du_up_168 v0 v1
  = case coe v0 of
      C_act_154 -> coe du_emb_126 (coe v1)
      C_eff_156 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.LTy
d_LTy_174 a0 = ()
data T_LTy_174
  = C_One_176 | C_Zero_178 | C__'8855't__180 T_LTy_174 T_LTy_174 |
    C__'8853't__182 T_LTy_174 T_LTy_174 | C_Ct_184 Integer T_LTy_174 |
    C_Fn_186 T_Kd_146 T_Gr_152 T_LTy_174 T_LTy_174 |
    C_Nu_188 T_LF_130 | C_μt_190 T_LF_130 |
    C_Bt_192 MAlonzo.Code.Once.LinCore.Flat.T_Base_46
-- Once.LinCore.Core.LF∙
d_LF'8729'_194 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 -> T_LTy_174 -> T_LTy_174
d_LF'8729'_194 ~v0 v1 v2 = du_LF'8729'_194 v1 v2
du_LF'8729'_194 :: T_LF_130 -> T_LTy_174 -> T_LTy_174
du_LF'8729'_194 v0 v1
  = case coe v0 of
      C_Idf_132 -> coe v1
      C_Kone_134 -> coe C_One_176
      C_Kzero_136 -> coe C_Zero_178
      C_Kb_138 v2 -> coe C_Bt_192 (coe v2)
      C_Kμ_140 v2 -> coe C_μt_190 (coe v2)
      C__'8853'f__142 v2 v3
        -> coe
             C__'8853't__182 (coe du_LF'8729'_194 (coe v2) (coe v1))
             (coe du_LF'8729'_194 (coe v3) (coe v1))
      C__'8855'f__144 v2 v3
        -> coe
             C__'8855't__180 (coe du_LF'8729'_194 (coe v2) (coe v1))
             (coe du_LF'8729'_194 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.FS
d_FS_222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 -> () -> ()
d_FS_222 = erased
-- Once.LinCore.Core.Mu
d_Mu_226 a0 a1 = ()
newtype T_Mu_226 = C_inμ_256 AgdaAny
-- Once.LinCore.Core.outμ
d_outμ_260 :: T_Mu_226 -> AgdaAny
d_outμ_260 v0
  = case coe v0 of
      C_inμ_256 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Nuᵐ
d_Nu'7504'_266 a0 a1 = ()
data T_Nu'7504'_266
  = C_constructor_274 MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
-- Once.LinCore.Core.Nuᵐ.outν
d_outν_272 ::
  T_Nu'7504'_266 -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_outν_272 v0
  = case coe v0 of
      C_constructor_274 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.anaN
d_anaN_280 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_Nu'7504'_266
d_anaN_280 v0 v1 ~v2 v3 v4 = du_anaN_280 v0 v1 v3 v4
du_anaN_280 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_Nu'7504'_266
du_anaN_280 v0 v1 v2 v3
  = coe
      C_constructor_274
      (coe du_treeN_286 (coe v0) (coe v1) (coe v2) (coe v2 v3))
-- Once.LinCore.Core.treeN
d_treeN_286 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_treeN_286 v0 v1 ~v2 v3 v4 = du_treeN_286 v0 v1 v3 v4
du_treeN_286 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_treeN_286 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
             (coe du_mapN_294 (coe v0) (coe v1) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v4) (coe v5)
             (coe
                (\ v7 -> coe du_treeN_286 (coe v0) (coe v1) (coe v2) (coe v6 v7)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.mapN
d_mapN_294 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  T_LF_130 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> AgdaAny
d_mapN_294 v0 v1 v2 ~v3 v4 v5 = du_mapN_294 v0 v1 v2 v4 v5
du_mapN_294 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  T_LF_130 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> AgdaAny
du_mapN_294 v0 v1 v2 v3 v4
  = case coe v2 of
      C_Idf_132 -> coe du_anaN_280 (coe v0) (coe v1) (coe v3) (coe v4)
      C_Kone_134 -> coe v4
      C_Kb_138 v5 -> coe v4
      C_Kμ_140 v5 -> coe v4
      C__'8853'f__142 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapN_294 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapN_294 (coe v0) (coe v1) (coe v6) (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'f__144 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapN_294 (coe v0) (coe v1) (coe v5) (coe v3) (coe v7))
                    (coe du_mapN_294 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.⟦_⟧
d_'10214'_'10215'_392 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_LTy_174 -> ()
d_'10214'_'10215'_392 = erased
-- Once.LinCore.Core.coh
d_coh_424 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 -> T_LTy_174 -> AgdaAny -> AgdaAny
d_coh_424 ~v0 v1 ~v2 v3 = du_coh_424 v1 v3
du_coh_424 :: T_LF_130 -> AgdaAny -> AgdaAny
du_coh_424 v0 v1
  = case coe v0 of
      C_Idf_132 -> coe v1
      C_Kone_134 -> coe v1
      C_Kb_138 v2 -> coe v1
      C_Kμ_140 v2 -> coe v1
      C__'8853'f__142 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coh_424 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coh_424 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'f__144 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coh_424 (coe v2) (coe v4))
                    (coe du_coh_424 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.coh⁻¹
d_coh'8315''185'_478 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 -> T_LTy_174 -> AgdaAny -> AgdaAny
d_coh'8315''185'_478 ~v0 v1 ~v2 v3 = du_coh'8315''185'_478 v1 v3
du_coh'8315''185'_478 :: T_LF_130 -> AgdaAny -> AgdaAny
du_coh'8315''185'_478 v0 v1
  = case coe v0 of
      C_Idf_132 -> coe v1
      C_Kone_134 -> coe v1
      C_Kb_138 v2 -> coe v1
      C_Kμ_140 v2 -> coe v1
      C__'8853'f__142 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coh'8315''185'_478 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coh'8315''185'_478 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'f__144 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coh'8315''185'_478 (coe v2) (coe v4))
                    (coe du_coh'8315''185'_478 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.⌜_⌝
d_'8988'_'8989'_528 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> T_LTy_174
d_'8988'_'8989'_528 ~v0 v1 = du_'8988'_'8989'_528 v1
du_'8988'_'8989'_528 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> T_LTy_174
du_'8988'_'8989'_528 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe C_One_176
      MAlonzo.Code.Once.LinCore.Flat.C_fvoid_14 -> coe C_Zero_178
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v1 -> coe C_Bt_192 (coe v1)
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v1 v2
        -> coe
             C__'8855't__180 (coe du_'8988'_'8989'_528 (coe v1))
             (coe du_'8988'_'8989'_528 (coe v2))
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v1 v2
        -> coe
             C__'8853't__182 (coe du_'8988'_'8989'_528 (coe v1))
             (coe du_'8988'_'8989'_528 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.toF
d_toF_542 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
d_toF_542 ~v0 v1 v2 = du_toF_542 v1 v2
du_toF_542 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
du_toF_542 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_toF_542 (coe v2) (coe v4))
                    (coe du_toF_542 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_toF_542 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_toF_542 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.fromF
d_fromF_572 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
d_fromF_572 ~v0 v1 v2 = du_fromF_572 v1 v2
du_fromF_572 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> AgdaAny
du_fromF_572 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_fromF_572 (coe v2) (coe v4))
                    (coe du_fromF_572 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_fromF_572 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_fromF_572 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.flat
d_flat_602 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_flat_602 ~v0 v1 v2 = du_flat_602 v1 v2
du_flat_602 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_flat_602 v0 v1
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
                    (coe du_flat_602 (coe v6) (coe v4))
                    (coe du_flat_602 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v6 v7
               -> coe
                    MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20
                    (coe du_flat_602 (coe v6) (coe v4))
                    (coe du_flat_602 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.toV
d_toV_616 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_toV_616 ~v0 v1 v2 = du_toV_616 v1 v2
du_toV_616 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
du_toV_616 v0 v1
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
                                (coe du_toV_616 v6 v4 v9) (coe du_toV_616 v7 v5 v10)
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
                                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe du_toV_616 v6 v4 v9)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                           -> coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe du_toV_616 v7 v5 v9)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.fromV
d_fromV_648 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_fromV_648 ~v0 v1 v2 = du_fromV_648 v1 v2
du_fromV_648 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
du_fromV_648 v0 v1
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
                                (coe du_fromV_648 v6 v4 v9) (coe du_fromV_648 v7 v5 v10)
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
                                (coe du_fromV_648 v6 v4 v9)
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                           -> coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                (coe du_fromV_648 v7 v5 v9)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sig
d_Sig_676 a0 = ()
data T_Sig_676
  = C_sig_690 MAlonzo.Code.Once.Spec.Type.T_Ty_8
              MAlonzo.Code.Once.Spec.Type.T_Ty_8
              MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
-- Once.LinCore.Core.Sig.sA
d_sA_684 :: T_Sig_676 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_684 v0
  = case coe v0 of
      C_sig_690 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sig.sB
d_sB_686 :: T_Sig_676 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_686 v0
  = case coe v0 of
      C_sig_690 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sig.info
d_info_688 ::
  T_Sig_676 -> MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_688 v0
  = case coe v0 of
      C_sig_690 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.sdom
d_sdom_692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Sig_676 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_692 ~v0 v1 = du_sdom_692 v1
du_sdom_692 :: T_Sig_676 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_692 v0
  = coe
      du_flat_602 (coe d_sA_684 (coe v0))
      (coe
         MAlonzo.Code.Once.SigOp.Info.d_baseA_120 (coe d_info_688 (coe v0)))
-- Once.LinCore.Core.scod
d_scod_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Sig_676 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_694 ~v0 v1 = du_scod_694 v1
du_scod_694 :: T_Sig_676 -> MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_694 v0
  = coe
      du_flat_602 (coe d_sB_686 (coe v0))
      (coe
         MAlonzo.Code.Once.SigOp.Info.d_conB_122 (coe d_info_688 (coe v0)))
-- Once.LinCore.Core.Sg
d_Sg_700 a0 = ()
data T_Sg_700
  = C_sg_722 T_Kd_146 T_Gr_152 T_LTy_174 T_LTy_174 T_LTy_174
-- Once.LinCore.Core.Sg.kd
d_kd_712 :: T_Sg_700 -> T_Kd_146
d_kd_712 v0
  = case coe v0 of
      C_sg_722 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.gr
d_gr_714 :: T_Sg_700 -> T_Gr_152
d_gr_714 v0
  = case coe v0 of
      C_sg_722 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.env
d_env_716 :: T_Sg_700 -> T_LTy_174
d_env_716 v0
  = case coe v0 of
      C_sg_722 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.dom
d_dom_718 :: T_Sg_700 -> T_LTy_174
d_dom_718 v0
  = case coe v0 of
      C_sg_722 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Sg.cod
d_cod_720 :: T_Sg_700 -> T_LTy_174
d_cod_720 v0
  = case coe v0 of
      C_sg_722 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.Cx
d_Cx_724 a0 = ()
data T_Cx_724 = C_ε_726 | C__'9656'__728 T_Cx_724 T_Sg_700
-- Once.LinCore.Core.len
d_len_730 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 -> Integer
d_len_730 ~v0 v1 = du_len_730 v1
du_len_730 :: T_Cx_724 -> Integer
du_len_730 v0
  = case coe v0 of
      C_ε_726 -> coe (0 :: Integer)
      C__'9656'__728 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_len_730 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core._∋[_]_
d__'8715''91'_'93'__734 a0 a1 a2 a3 = ()
data T__'8715''91'_'93'__734
  = C_here_740 | C_there_750 T__'8715''91'_'93'__734
-- Once.LinCore.Core.Tm
d_Tm_754 a0 a1 a2 a3 a4 = ()
data T_Tm_754
  = C_lid_782 | C__'8728'l__792 T_LTy_174 T_Tm_754 T_Tm_754 |
    C__'8855'l__804 T_Tm_754 T_Tm_754 | C_ρl_810 | C_ρl'8315'_816 |
    C_lul_822 | C_lul'8315'_828 | C_lassoc_838 | C_lassoc'8315'_848 |
    C_lswap_856 | C_dup_862 | C_drop_868 | C_linl_876 | C_linr_884 |
    C_lcase_894 T_Tm_754 T_Tm_754 | C_lzero_900 | C_lIn_906 |
    C_lOutμ_912 | C_lcata_920 T_Tm_754 |
    C_lclo_938 T_LF_130 Integer T_Kd_146 T_Gr_152 T_LTy_174 T_LTy_174
               T_LTy_174 T__'8715''91'_'93'__734 |
    C_lapp_952 T_Gr_152 T__'8715''91'_'93'__734 | C_lend_962 T_Tm_754 |
    C_blift_970 T_Tm_754 | C_bfst_980 T_Tm_754 | C_bsnd_990 T_Tm_754 |
    C_bcaseE_1000 T_Tm_754 T_Tm_754 | C_bout_1008 T_Tm_754 |
    C_bcopy_1012 | C_bapp_1024 T_Gr_152 T__'8715''91'_'93'__734 |
    C_llam_1038 T_Tm_754 AgdaAny | C_llamω_1052 T_Tm_754 AgdaAny |
    C_lev_1062 | C_bev_1070 | C_lunf_1078 | C_lout_1084 |
    C_lconst_1090 AgdaAny | C_lop_1096 T_Sig_676 |
    C_liter_1106 T_Tm_754 T_Blk_764
-- Once.LinCore.Core.Blk
d_Blk_764 a0 a1 a2 a3 a4 a5 = ()
data T_Blk_764
  = C_k'45'id_1114 | C_k'45''8728'_1128 T_Blk_764 T_Blk_764 |
    C_k'45''8855'_1144 T_Blk_764 T_Blk_764 | C_k'45'ρ_1150 |
    C_k'45'ρ'8315'_1156 | C_k'45'lul_1162 | C_k'45'lul'8315'_1168 |
    C_k'45'assoc_1178 | C_k'45'assoc'8315'_1188 | C_k'45'swap_1196 |
    C_k'45'dup_1202 | C_k'45'drop_1208 | C_k'45'inl_1216 |
    C_k'45'inr_1224 | C_k'45'case_1238 T_Blk_764 T_Blk_764 |
    C_k'45'zero_1244 | C_k'45'in_1250 | C_k'45'out_1256 |
    C_k'45'cata_1266 T_Blk_764 | C_k'45'clo_1286 | C_k'45'app_1300 |
    C_k'45'lend_1312 T_Blk_764 | C_k'45'lift_1322 T_Blk_764 |
    C_k'45'fst_1334 T_Blk_764 | C_k'45'snd_1346 T_Blk_764 |
    C_k'45'caseE_1360 T_Blk_764 T_Blk_764 |
    C_k'45'bout_1370 T_Blk_764 | C_k'45'copy_1374 | C_k'45'bapp_1386 |
    C_k'45'lam_1402 | C_k'45'lamω_1418 | C_k'45'ev_1426 |
    C_k'45'bev_1432 | C_k'45'unf_1440 | C_k'45'nout_1446 |
    C_k'45'const_1454 | C_k'45'op_1460
-- Once.LinCore.Core.Gd
d_Gd_774 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 ->
  T_LTy_174 -> T_LTy_174 -> T_LTy_174 -> T_Gr_152 -> T_Tm_754 -> ()
d_Gd_774 = erased
-- Once.LinCore.Core.LTm
d_LTm_1462 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 -> T_LTy_174 -> T_LTy_174 -> ()
d_LTm_1462 = erased
-- Once.LinCore.Core.Coalg
d_Coalg_1466 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 -> T_LTy_174 -> T_LTy_174
d_Coalg_1466 ~v0 v1 v2 = du_Coalg_1466 v1 v2
du_Coalg_1466 :: T_LF_130 -> T_LTy_174 -> T_LTy_174
du_Coalg_1466 v0 v1
  = coe
      C_Fn_186 (coe C_many_150) (coe C_act_154) (coe v1)
      (coe du_LF'8729'_194 (coe v0) (coe v1))
-- Once.LinCore.Core.strL
d_strL_1480 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 -> T_LF_130 -> T_LF_130 -> T_LTy_174 -> T_Tm_754
d_strL_1480 ~v0 ~v1 v2 v3 v4 = du_strL_1480 v2 v3 v4
du_strL_1480 :: T_LF_130 -> T_LF_130 -> T_LTy_174 -> T_Tm_754
du_strL_1480 v0 v1 v2
  = case coe v1 of
      C_Idf_132
        -> coe
             C__'8728'l__792 (coe C__'8855't__180 (coe C_One_176) (coe v2))
             (coe
                C__'8855'l__804 (coe C_bsnd_990 (coe C_bcopy_1012))
                (coe C_lid_782))
             (coe C_lul'8315'_828)
      C_Kone_134 -> coe C_lid_782
      C_Kzero_136 -> coe C_lid_782
      C_Kb_138 v3 -> coe C_lid_782
      C_Kμ_140 v3 -> coe C_lid_782
      C__'8853'f__142 v3 v4
        -> coe
             C_lcase_894
             (coe
                C__'8728'l__792
                (coe
                   du_LF'8729'_194 (coe v3)
                   (coe
                      C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v2)) (coe v2)))
                (coe C_linl_876) (coe du_strL_1480 (coe v0) (coe v3) (coe v2)))
             (coe
                C__'8728'l__792
                (coe
                   du_LF'8729'_194 (coe v4)
                   (coe
                      C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v2)) (coe v2)))
                (coe C_linr_884) (coe du_strL_1480 (coe v0) (coe v4) (coe v2)))
      C__'8855'f__144 v3 v4
        -> coe
             C__'8855'l__804 (coe du_strL_1480 (coe v0) (coe v3) (coe v2))
             (coe du_strL_1480 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.mapNu
d_mapNu_1530 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 -> T_LF_130 -> T_LF_130 -> T_LTy_174 -> T_Tm_754
d_mapNu_1530 ~v0 ~v1 v2 v3 ~v4 = du_mapNu_1530 v2 v3
du_mapNu_1530 :: T_LF_130 -> T_LF_130 -> T_Tm_754
du_mapNu_1530 v0 v1
  = case coe v1 of
      C_Idf_132 -> coe C_lunf_1078
      C_Kone_134 -> coe C_lid_782
      C_Kzero_136 -> coe C_lid_782
      C_Kb_138 v2 -> coe C_lid_782
      C_Kμ_140 v2 -> coe C_lid_782
      C__'8853'f__142 v2 v3
        -> coe
             C_lcase_894
             (coe
                C__'8728'l__792
                (coe du_LF'8729'_194 (coe v2) (coe C_Nu_188 (coe v0)))
                (coe C_linl_876) (coe du_mapNu_1530 (coe v0) (coe v2)))
             (coe
                C__'8728'l__792
                (coe du_LF'8729'_194 (coe v3) (coe C_Nu_188 (coe v0)))
                (coe C_linr_884) (coe du_mapNu_1530 (coe v0) (coe v3)))
      C__'8855'f__144 v2 v3
        -> coe
             C__'8855'l__804 (coe du_mapNu_1530 (coe v0) (coe v2))
             (coe du_mapNu_1530 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Core.obsT
d_obsT_1578 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 -> T_LF_130 -> T_LTy_174 -> T_Tm_754
d_obsT_1578 ~v0 ~v1 v2 v3 = du_obsT_1578 v2 v3
du_obsT_1578 :: T_LF_130 -> T_LTy_174 -> T_Tm_754
du_obsT_1578 v0 v1
  = coe
      C__'8728'l__792
      (coe
         du_LF'8729'_194 (coe v0)
         (coe
            C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v1)) (coe v1)))
      (coe du_mapNu_1530 (coe v0) (coe v0))
      (coe
         C__'8728'l__792
         (coe
            C__'8855't__180 (coe C_One_176)
            (coe
               du_LF'8729'_194 (coe v0)
               (coe
                  C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v1)) (coe v1))))
         (coe C_lul_822)
         (coe
            C__'8728'l__792
            (coe
               C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v1))
               (coe
                  du_LF'8729'_194 (coe v0)
                  (coe
                     C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v1)) (coe v1))))
            (coe C__'8855'l__804 (coe C_drop_868) (coe C_lid_782))
            (coe
               C__'8728'l__792
               (coe
                  C__'8855't__180 (coe du_Coalg_1466 (coe v0) (coe v1))
                  (coe du_LF'8729'_194 (coe v0) (coe v1)))
               (coe C_lend_962 (coe du_strL_1480 (coe v0) (coe v0) (coe v1)))
               (coe C_lend_962 (coe C_bsnd_990 (coe C_bev_1070))))))
-- Once.LinCore.Core.cohc
d_cohc_1588 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  T_LTy_174 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_cohc_1588 ~v0 v1 ~v2 v3 v4 = du_cohc_1588 v1 v3 v4
du_cohc_1588 ::
  T_LF_130 ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_cohc_1588 v0 v1 v2
  = coe du_fmapT_98 (coe du_coh_424 (coe v0)) (coe v1 v2)
-- Once.LinCore.Core.lana
d_lana_1608 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 ->
  Integer ->
  T_LTy_174 ->
  T_LTy_174 -> T_LTy_174 -> T__'8715''91'_'93'__734 -> T_Tm_754
d_lana_1608 ~v0 ~v1 v2 v3 v4 ~v5 v6 = du_lana_1608 v2 v3 v4 v6
du_lana_1608 ::
  Integer ->
  T_LTy_174 -> T_LTy_174 -> T__'8715''91'_'93'__734 -> T_Tm_754
du_lana_1608 v0 v1 v2 v3
  = coe
      C_lclo_938 (coe C_Idf_132) v0 (coe C_once_148) (coe C_act_154) v1
      (coe C_One_176) v2 v3
-- Once.LinCore.Core.lobs
d_lobs_1622 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  T_Cx_724 ->
  Integer ->
  T_LTy_174 -> T_LTy_174 -> T__'8715''91'_'93'__734 -> T_Tm_754
d_lobs_1622 ~v0 v1 ~v2 v3 v4 ~v5 v6 = du_lobs_1622 v1 v3 v4 v6
du_lobs_1622 ::
  T_LF_130 ->
  Integer -> T_LTy_174 -> T__'8715''91'_'93'__734 -> T_Tm_754
du_lobs_1622 v0 v1 v2 v3
  = coe
      C__'8728'l__792 (coe du_LF'8729'_194 (coe v0) (coe v2))
      (coe
         C_lclo_938 v0 v1 (coe C_once_148) (coe C_act_154) v2
         (coe C_One_176) (coe du_LF'8729'_194 (coe v0) (coe v2)) v3)
      (coe
         C__'8728'l__792
         (coe
            C__'8855't__180 (coe C_Ct_184 (coe v1) (coe v2)) (coe C_One_176))
         (coe C_lapp_952 (coe C_act_154) v3) (coe C_ρl'8315'_816))
-- Once.LinCore.Core.k-obs
d_k'45'obs_1640 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_LF_130 ->
  T_Cx_724 ->
  Integer ->
  T_LTy_174 -> T_LTy_174 -> T__'8715''91'_'93'__734 -> T_Blk_764
d_k'45'obs_1640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_k'45'obs_1640
du_k'45'obs_1640 :: T_Blk_764
du_k'45'obs_1640
  = coe
      C_k'45''8728'_1128 (coe C_k'45'clo_1286)
      (coe
         C_k'45''8728'_1128 (coe C_k'45'app_1300) (coe C_k'45'ρ'8315'_1156))
-- Once.LinCore.Core.Body
d_Body_1650 a0 a1 a2 = ()
data T_Body_1650
  = C_b1_1664 T_Tm_754 AgdaAny | C_bω_1676 T_Tm_754 AgdaAny
-- Once.LinCore.Core.Defs
d_Defs_1678 a0 a1 = ()
data T_Defs_1678
  = C_ε_1680 | C__'9656'__1686 T_Defs_1678 T_Body_1650
-- Once.LinCore.Core.Look
d_Look_1696 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Look_1696
  = C_lk'45'here_1706 | C_lk'45'there_1728 T_Look_1696
-- Once.LinCore.Core.Env
d_Env_1730 a0 a1 = ()
data T_Env_1730
  = C_ε_1732 |
    C__'9656'__1738 T_Env_1730 (AgdaAny -> AgdaAny -> AgdaAny)
-- Once.LinCore.Core.lookup
d_lookup_1746 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Cx_724 ->
  Integer ->
  T_Sg_700 ->
  T_Env_1730 ->
  T__'8715''91'_'93'__734 -> AgdaAny -> AgdaAny -> AgdaAny
d_lookup_1746 ~v0 v1 ~v2 ~v3 v4 v5 = du_lookup_1746 v1 v4 v5
du_lookup_1746 ::
  T_Cx_724 ->
  T_Env_1730 ->
  T__'8715''91'_'93'__734 -> AgdaAny -> AgdaAny -> AgdaAny
du_lookup_1746 v0 v1 v2
  = case coe v1 of
      C_ε_1732 -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      C__'9656'__1738 v5 v6
        -> case coe v0 of
             C__'9656'__728 v7 v8
               -> case coe v2 of
                    C_here_740 -> coe v6
                    C_there_750 v13 -> coe du_lookup_1746 (coe v7) (coe v5) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
