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

module MAlonzo.Code.Once.LinCore.Values where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

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
-- Once.LinCore.Values._.Coalg
d_Coalg_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_Coalg_88 ~v0 ~v1 = du_Coalg_88
du_Coalg_88 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_Coalg_88 = coe MAlonzo.Code.Once.LinCore.Core.du_Coalg_1470
-- Once.LinCore.Values._.Defs
d_Defs_94 a0 a1 a2 = ()
-- Once.LinCore.Values._.Gd
d_Gd_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> ()
d_Gd_102 = erased
-- Once.LinCore.Values._.Gr
d_Gr_104 a0 a1 = ()
-- Once.LinCore.Values._.Kd
d_Kd_110 a0 a1 = ()
-- Once.LinCore.Values._.LF
d_LF_118 a0 a1 = ()
-- Once.LinCore.Values._.LF∙
d_LF'8729'_120 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_LF'8729'_120 ~v0 ~v1 = du_LF'8729'_120
du_LF'8729'_120 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_LF'8729'_120
  = coe MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
-- Once.LinCore.Values._.LTy
d_LTy_124 a0 a1 = ()
-- Once.LinCore.Values._.Tm
d_Tm_148 a0 a1 a2 a3 a4 a5 = ()
-- Once.LinCore.Values._.⌜_⌝
d_'8988'_'8989'_390 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_390 ~v0 ~v1 = du_'8988'_'8989'_390
du_'8988'_'8989'_390 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_390
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.Values._.⟦_⟧f
d_'10214'_'10215'f_394 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> ()
d_'10214'_'10215'f_394 = erased
-- Once.LinCore.Values.words
d_words_662 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_words_662 ~v0 v1 v2 = du_words_662 v1 v2
du_words_662 ::
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_words_662 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v2 v3
        -> coe
             addInt (coe du_words_662 (coe v0) (coe v2))
             (coe du_words_662 (coe v0) (coe v3))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v2 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                (coe du_words_662 (coe v0) (coe v2))
                (coe du_words_662 (coe v0) (coe v3)))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v2 v3
        -> coe du_words_662 (coe v0) (coe v3)
      MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v2 v3 v4 v5
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_μt_194 v2 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Bt_196 v2 -> coe v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.szμ
d_szμ_690 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Integer
d_szμ_690 ~v0 v1 v2 = du_szμ_690 v1 v2
du_szμ_690 ::
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Integer
du_szμ_690 v0 v1
  = coe
      du_words_662 (coe v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v1)
         (coe MAlonzo.Code.Once.LinCore.Core.C_μt_194 (coe v1)))
-- Once.LinCore.Values.szc
d_szc_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_szc_694 ~v0 v1 v2 = du_szc_694 v1 v2
du_szc_694 ::
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_szc_694 v0 v1
  = coe
      addInt (coe (1 :: Integer)) (coe du_words_662 (coe v0) (coe v1))
-- Once.LinCore.Values.szν
d_szν_698 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_szν_698 ~v0 v1 v2 v3 = du_szν_698 v1 v2 v3
du_szν_698 ::
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_szν_698 v0 v1 v2
  = coe
      du_words_662 (coe v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_Coalg_1470 (coe v1) (coe v2))
         (coe v2))
-- Once.LinCore.Values.Id
d_Id_704 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> ()
d_Id_704 = erased
-- Once.LinCore.Values.serial
d_serial_706 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_serial_706 ~v0 ~v1 v2 = du_serial_706 v2
du_serial_706 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_serial_706 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.LinCore.Values._≟ᵢ_
d__'8799''7522'__712 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''7522'__712 ~v0 ~v1 v2 v3 = du__'8799''7522'__712 v2 v3
du__'8799''7522'__712 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799''7522'__712 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                               (coe eqInt (coe v3) (coe v5))) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (let v9
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v9 ->
                                                   coe
                                                     MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                     (coe v2))
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                   (coe eqInt (coe v2) (coe v4))) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                             -> if coe v10
                                                  then coe
                                                         seq (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                               erased))
                                                  else coe
                                                         seq (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v7)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.Lam
d_Lam_770 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Lam_770
  = C_c1_784 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
             MAlonzo.Code.Once.LinCore.Core.T_Defs_1682
             MAlonzo.Code.Once.LinCore.Core.T_Tm_758 AgdaAny |
    C_cω_798 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
             MAlonzo.Code.Once.LinCore.Core.T_Defs_1682
             MAlonzo.Code.Once.LinCore.Core.T_Tm_758 AgdaAny
-- Once.LinCore.Values.MV
d_MV_800 a0 a1 a2 = ()
data T_MV_800
  = C_mone_802 | C_mpair_808 T_MV_800 T_MV_800 |
    C_minl_814 T_MV_800 | C_minr_820 T_MV_800 | C_mbase_824 AgdaAny |
    C_mmu_828 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_MV_800 |
    C_mct_834 T_MV_800 |
    C_mfn_846 MAlonzo.Code.Once.LinCore.Core.T_LTy_178
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Lam_770 T_MV_800 |
    C_mnu_852 MAlonzo.Code.Once.LinCore.Core.T_LTy_178
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_MV_800
-- Once.LinCore.Values.mvF
d_mvF_856 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> T_MV_800
d_mvF_856 ~v0 ~v1 v2 v3 = du_mvF_856 v2 v3
du_mvF_856 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> T_MV_800
du_mvF_856 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe C_mone_802
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v2 -> coe C_mbase_824 v1
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_mpair_808 (coe du_mvF_856 (coe v2) (coe v4))
                    (coe du_mvF_856 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe C_minl_814 (coe du_mvF_856 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe C_minr_820 (coe du_mvF_856 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.TEv
d_TEv_884 a0 a1 = ()
data T_TEv_884 = C_tnew_886 Integer | C_tdel_888 Integer
-- Once.LinCore.Values.Ev
d_Ev_890 a0 a1 = ()
data T_Ev_890
  = C_alloc_892 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_free_894 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_peek_896 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_io_900 MAlonzo.Code.Once.IR.Semantics.Trace.T_CallOp_58 AgdaAny
             AgdaAny |
    C_stp_904 MAlonzo.Code.Once.IR.Semantics.Trace.T_HaltOp_78
              AgdaAny |
    C_tmp_906 T_TEv_884
-- Once.LinCore.Values.Trace
d_Trace_908 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> ()
d_Trace_908 = erased
-- Once.LinCore.Values.copy
d_copy_912 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_MV_800 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_copy_912 ~v0 v1 v2 v3 v4 = du_copy_912 v1 v2 v3 v4
du_copy_912 ::
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_MV_800 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_copy_912 v0 v1 v2 v3
  = case coe v2 of
      C_mone_802
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      C_mpair_808 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> let v10 = coe du_copy_912 (coe v0) (coe v8) (coe v6) (coe v3) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> case coe v12 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> let v15
                                         = coe du_copy_912 (coe v0) (coe v9) (coe v7) (coe v13) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                          -> case coe v17 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe C_mpair_808 v11 v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v18)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v14) (coe v19)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minl_814 v6
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v7 v8
               -> let v9 = coe du_copy_912 (coe v0) (coe v7) (coe v6) (coe v3) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> coe
                              seq (coe v11)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_minl_814 v10)
                                 (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minr_820 v6
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v7 v8
               -> let v9 = coe du_copy_912 (coe v0) (coe v8) (coe v6) (coe v3) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> coe
                              seq (coe v11)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_minr_820 v10)
                                 (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mbase_824 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_mbase_824 v5)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      C_mmu_828 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_μt_194 v7
               -> let v8
                        = coe
                            du_copy_912 (coe v0)
                            (coe
                               MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v7) (coe v1))
                            (coe v6) (coe v3) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v10 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_mmu_828
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe du_szμ_690 (coe v0) (coe v7)) (coe v11))
                                        v9)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe addInt (coe (1 :: Integer)) (coe v11))
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v12)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 C_alloc_892
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe du_szμ_690 (coe v0) (coe v7)) (coe v11)))
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mct_834 v6
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v7 v8
               -> let v9 = coe du_copy_912 (coe v0) (coe v8) (coe v6) (coe v3) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> coe
                              seq (coe v11)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_mct_834 v10)
                                 (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mfn_846 v6 v9 v10 v11
        -> let v12
                 = coe du_copy_912 (coe v0) (coe v6) (coe v11) (coe v3) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> case coe v14 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_mfn_846 v6
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe du_szc_694 (coe v0) (coe v6)) (coe v15))
                                 v10 v13)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe addInt (coe (1 :: Integer)) (coe v15))
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v16)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          C_alloc_892
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe du_szc_694 (coe v0) (coe v6)) (coe v15)))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_mnu_852 v5 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v8
               -> let v9
                        = coe
                            du_copy_912 (coe v0)
                            (coe
                               MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                               (coe
                                  MAlonzo.Code.Once.LinCore.Core.du_Coalg_1470 (coe v8) (coe v5))
                               (coe v5))
                            (coe v7) (coe v3) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> case coe v11 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_mnu_852 v5
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe du_szν_698 (coe v0) (coe v8) (coe v5)) (coe v12))
                                        v10)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe addInt (coe (1 :: Integer)) (coe v12))
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v13)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 C_alloc_892
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe du_szν_698 (coe v0) (coe v8) (coe v5))
                                                    (coe v12)))
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.freeAll
d_freeAll_1106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_MV_800 -> [T_Ev_890]
d_freeAll_1106 ~v0 ~v1 v2 v3 = du_freeAll_1106 v2 v3
du_freeAll_1106 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_MV_800 -> [T_Ev_890]
du_freeAll_1106 v0 v1
  = case coe v1 of
      C_mone_802 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_mpair_808 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_freeAll_1106 (coe v6) (coe v4))
                    (coe du_freeAll_1106 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minl_814 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v5 v6
               -> coe du_freeAll_1106 (coe v5) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minr_820 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v5 v6
               -> coe du_freeAll_1106 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mbase_824 v3 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_mmu_828 v3 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_μt_194 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_free_894 (coe v3))
                    (coe
                       du_freeAll_1106
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v5) (coe v0))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mct_834 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v5 v6
               -> coe du_freeAll_1106 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mfn_846 v4 v7 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_free_894 (coe v7)) (coe du_freeAll_1106 (coe v4) (coe v9))
      C_mnu_852 v3 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_free_894 (coe v4))
                    (coe
                       du_freeAll_1106
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_Coalg_1470 (coe v6) (coe v3))
                          (coe v3))
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.tag
d_tag_1140 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> T_MV_800 -> T_MV_800
d_tag_1140 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_tag_1140 v4 v5
du_tag_1140 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> T_MV_800 -> T_MV_800
du_tag_1140 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe C_mct_834 v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v2 v3
        -> case coe v1 of
             C_minl_814 v6 -> coe C_minl_814 (coe du_tag_1140 (coe v2) (coe v6))
             C_minr_820 v6 -> coe C_minr_820 (coe du_tag_1140 (coe v3) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> case coe v1 of
             C_mpair_808 v6 v7
               -> coe
                    C_mpair_808 (coe du_tag_1140 (coe v2) (coe v6))
                    (coe du_tag_1140 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.TL
d_TL_1174 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> ()
d_TL_1174 = erased
-- Once.LinCore.Values.none
d_none_1176 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer -> Integer
d_none_1176 ~v0 ~v1 ~v2 = du_none_1176
du_none_1176 :: Integer
du_none_1176 = coe (0 :: Integer)
-- Once.LinCore.Values.δn
d_δn_1178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer -> Integer -> Integer
d_δn_1178 ~v0 ~v1 v2 v3 = du_δn_1178 v2 v3
du_δn_1178 :: Integer -> Integer -> Integer
du_δn_1178 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe eqInt (coe v0) (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe seq (coe v4) (coe (1 :: Integer))
                else coe seq (coe v4) (coe (0 :: Integer))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.LinCore.Values.tstep
d_tstep_1196 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Ev_890 -> (Integer -> Integer) -> Integer -> Integer
d_tstep_1196 ~v0 ~v1 v2 v3 = du_tstep_1196 v2 v3
du_tstep_1196 ::
  T_Ev_890 -> (Integer -> Integer) -> Integer -> Integer
du_tstep_1196 v0 v1
  = case coe v0 of
      C_alloc_892 v2 -> coe v1
      C_free_894 v2 -> coe v1
      C_peek_896 v2 -> coe v1
      C_io_900 v2 v3 v4 -> coe v1
      C_stp_904 v2 v3 -> coe v1
      C_tmp_906 v2
        -> case coe v2 of
             C_tnew_886 v3
               -> coe
                    (\ v4 -> addInt (coe du_δn_1178 (coe v3) (coe v4)) (coe v1 v4))
             C_tdel_888 v3
               -> coe
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe v1 v4)
                         (coe du_δn_1178 (coe v3) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.tplay
d_tplay_1220 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_890] -> (Integer -> Integer) -> Integer -> Integer
d_tplay_1220 ~v0 ~v1 v2 v3 = du_tplay_1220 v2 v3
du_tplay_1220 ::
  [T_Ev_890] -> (Integer -> Integer) -> Integer -> Integer
du_tplay_1220 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldl_230
      (coe (\ v2 v3 -> coe du_tstep_1196 (coe v3) (coe v2))) (coe v1)
      (coe v0)
-- Once.LinCore.Values.tpre
d_tpre_1230 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Ev_890 -> (Integer -> Integer) -> ()
d_tpre_1230 = erased
-- Once.LinCore.Values.TOK
d_TOK_1250 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_890] -> (Integer -> Integer) -> ()
d_TOK_1250 = erased
-- Once.LinCore.Values.TLeg
d_TLeg_1256 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_890] -> ()
d_TLeg_1256 = erased
-- Once.LinCore.Values.TBal
d_TBal_1258 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_890] -> ()
d_TBal_1258 = erased
-- Once.LinCore.Values.tmps
d_tmps_1266 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_TEv_884] -> [T_Ev_890]
d_tmps_1266 ~v0 ~v1 = du_tmps_1266
du_tmps_1266 :: [T_TEv_884] -> [T_Ev_890]
du_tmps_1266
  = coe MAlonzo.Code.Data.List.Base.du_map_22 (coe C_tmp_906)
