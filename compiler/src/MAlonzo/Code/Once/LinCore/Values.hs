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
du_Coalg_88 = coe MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538
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
d_Tm_150 a0 a1 a2 a3 a4 a5 = ()
-- Once.LinCore.Values._.⌜_⌝
d_'8988'_'8989'_440 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_440 ~v0 ~v1 = du_'8988'_'8989'_440
du_'8988'_'8989'_440 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_440
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.Values._.⟦_⟧f
d_'10214'_'10215'f_444 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> ()
d_'10214'_'10215'f_444 = erased
-- Once.LinCore.Values.wsz
d_wsz_738 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_wsz_738 ~v0 ~v1 v2 = du_wsz_738 v2
du_wsz_738 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_wsz_738 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe addInt (coe du_wsz_738 (coe v1)) (coe du_wsz_738 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe du_wsz_738 (coe v1))
                (coe du_wsz_738 (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe du_wsz_738 (coe v2)
      MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v1 v2 v3 v4
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_μt_194 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Bt_196 v1 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.hdr
d_hdr_766 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> Integer
d_hdr_766 ~v0 ~v1 = du_hdr_766
du_hdr_766 :: Integer
du_hdr_766 = coe (5 :: Integer)
-- Once.LinCore.Values.szμ
d_szμ_768 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Integer
d_szμ_768 ~v0 ~v1 v2 = du_szμ_768 v2
du_szμ_768 :: MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Integer
du_szμ_768 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (1 :: Integer))
      (coe
         du_wsz_738
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_μt_194 (coe v0))))
-- Once.LinCore.Values.szc
d_szc_772 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_szc_772 ~v0 ~v1 v2 = du_szc_772 v2
du_szc_772 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_szc_772 v0
  = coe addInt (coe du_hdr_766) (coe du_wsz_738 (coe v0))
-- Once.LinCore.Values.szν
d_szν_776 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
d_szν_776 ~v0 ~v1 v2 v3 = du_szν_776 v2 v3
du_szν_776 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Integer
du_szν_776 v0 v1
  = coe
      addInt (coe du_hdr_766)
      (coe
         du_wsz_738
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
            (coe
               MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538 (coe v0) (coe v1))
            (coe v1)))
-- Once.LinCore.Values.Id
d_Id_782 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> ()
d_Id_782 = erased
-- Once.LinCore.Values.serial
d_serial_784 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_serial_784 ~v0 ~v1 v2 = du_serial_784 v2
du_serial_784 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_serial_784 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.LinCore.Values.≟ᵢ-k
d_'8799''7522''45'k_792 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799''7522''45'k_792 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8799''7522''45'k_792 v5
du_'8799''7522''45'k_792 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799''7522''45'k_792 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.≟ᵢ-n
d_'8799''7522''45'n_806 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799''7522''45'n_806 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_'8799''7522''45'n_806 v2 v3 v6
du_'8799''7522''45'n_806 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799''7522''45'n_806 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       du_'8799''7522''45'k_792
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v0)
                          (coe v1)))
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v3)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values._≟ᵢ_
d__'8799''7522'__824 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''7522'__824 ~v0 ~v1 v2 v3 = du__'8799''7522'__824 v2 v3
du__'8799''7522'__824 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799''7522'__824 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_'8799''7522''45'n_806 (coe v2) (coe v4)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.Lam
d_Lam_834 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Lam_834
  = C_c1_848 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
             MAlonzo.Code.Once.LinCore.Core.T_Defs_2078
             MAlonzo.Code.Once.LinCore.Core.T_Tm_758 AgdaAny |
    C_cω_862 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
             MAlonzo.Code.Once.LinCore.Core.T_Defs_2078
             MAlonzo.Code.Once.LinCore.Core.T_Tm_758 AgdaAny |
    C_cω'7580'_876 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
                   MAlonzo.Code.Once.LinCore.Core.T_Defs_2078
                   MAlonzo.Code.Once.LinCore.Core.T_Tm_758 AgdaAny
-- Once.LinCore.Values.once-of
d_once'45'of_886 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_Lam_834 -> T_Lam_834
d_once'45'of_886 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_once'45'of_886 v2 v3 v4 v5 v6
du_once'45'of_886 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_Lam_834 -> T_Lam_834
du_once'45'of_886 v0 v1 v2 v3 v4
  = case coe v4 of
      C_cω_862 v5 v10 v11 v12
        -> coe
             C_c1_848 v5 v10
             (coe
                MAlonzo.Code.Once.LinCore.Core.du_ownω_1990 (coe v1) (coe v2)
                (coe v3) (coe v11))
             (coe
                MAlonzo.Code.Once.LinCore.Core.du_own'45'gdb_2020 (coe v0) (coe v1)
                (coe v2) (coe v11) (coe v12))
      C_cω'7580'_876 v5 v10 v11 v12 -> coe C_c1_848 v5 v10 v11 v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.MV
d_MV_900 a0 a1 a2 = ()
data T_MV_900
  = C_mone_902 | C_mpair_908 T_MV_900 T_MV_900 |
    C_minl_914 T_MV_900 | C_minr_920 T_MV_900 | C_mbase_924 AgdaAny |
    C_mmu_928 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_MV_900 |
    C_mct_934 T_MV_900 |
    C_mfn_946 MAlonzo.Code.Once.LinCore.Core.T_LTy_178
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_Lam_834 T_MV_900 |
    C_mnu_952 MAlonzo.Code.Once.LinCore.Core.T_LTy_178
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 T_MV_900
-- Once.LinCore.Values.mvF
d_mvF_956 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> T_MV_900
d_mvF_956 ~v0 ~v1 v2 v3 = du_mvF_956 v2 v3
du_mvF_956 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 -> AgdaAny -> T_MV_900
du_mvF_956 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_funit_12 -> coe C_mone_902
      MAlonzo.Code.Once.LinCore.Flat.C_fw_16 v2 -> coe C_mbase_924 v1
      MAlonzo.Code.Once.LinCore.Flat.C__f'42'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_mpair_908 (coe du_mvF_956 (coe v2) (coe v4))
                    (coe du_mvF_956 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Flat.C__f'43'__20 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe C_minl_914 (coe du_mvF_956 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe C_minr_920 (coe du_mvF_956 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.TEv
d_TEv_984 a0 a1 = ()
data T_TEv_984 = C_tnew_986 Integer | C_tdel_988 Integer
-- Once.LinCore.Values.Ev
d_Ev_990 a0 a1 = ()
data T_Ev_990
  = C_alloc_992 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_free_994 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_peek_996 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 |
    C_io_1000 MAlonzo.Code.Once.IR.Semantics.Trace.T_CallOp_58 AgdaAny
              AgdaAny |
    C_stp_1004 MAlonzo.Code.Once.IR.Semantics.Trace.T_HaltOp_78
               AgdaAny |
    C_tmp_1006 T_TEv_984
-- Once.LinCore.Values.Trace
d_Trace_1008 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> ()
d_Trace_1008 = erased
-- Once.LinCore.Values.copy
d_copy_1012 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_MV_900 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_copy_1012 ~v0 ~v1 v2 v3 v4 = du_copy_1012 v2 v3 v4
du_copy_1012 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_MV_900 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_copy_1012 v0 v1 v2
  = case coe v1 of
      C_mone_902
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      C_mpair_908 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mpair_908
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_copy_1012 (coe v7) (coe v5) (coe v2)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             du_copy_1012 (coe v8) (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe du_copy_1012 (coe v7) (coe v5) (coe v2)))))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_copy_1012 (coe v8) (coe v6)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe du_copy_1012 (coe v7) (coe v5) (coe v2)))))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe du_copy_1012 (coe v7) (coe v5) (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012 (coe v8) (coe v6)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe du_copy_1012 (coe v7) (coe v5) (coe v2)))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minl_914 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_minl_914
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_copy_1012 (coe v6) (coe v5) (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_copy_1012 (coe v6) (coe v5) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minr_920 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_minr_920
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_copy_1012 (coe v7) (coe v5) (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_copy_1012 (coe v7) (coe v5) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mbase_924 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_mbase_924 v4)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      C_mmu_928 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_μt_194 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mmu_928
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe du_szμ_768 (coe v6))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v6)
                                      (coe v0))
                                   (coe v5) (coe v2)))))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             du_copy_1012
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v6) (coe v0))
                             (coe v5) (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v6)
                                      (coe v0))
                                   (coe v5) (coe v2)))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v6)
                                      (coe v0))
                                   (coe v5) (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                C_alloc_992
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe du_szμ_768 (coe v6))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_copy_1012
                                            (coe
                                               MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                               (coe v6) (coe v0))
                                            (coe v5) (coe v2))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mct_934 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mct_934
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_copy_1012 (coe v7) (coe v5) (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_copy_1012 (coe v7) (coe v5) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mfn_946 v5 v8 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_mfn_946 v5
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe du_szc_772 (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_copy_1012 (coe v5) (coe v10) (coe v2)))))
                v9
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_copy_1012 (coe v5) (coe v10) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_copy_1012 (coe v5) (coe v10) (coe v2)))))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_copy_1012 (coe v5) (coe v10) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         C_alloc_992
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe du_szc_772 (coe v5))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe du_copy_1012 (coe v5) (coe v10) (coe v2))))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      C_mnu_952 v4 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_mnu_952 v4
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe du_szν_776 (coe v7) (coe v4))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538 (coe v7)
                                         (coe v4))
                                      (coe v4))
                                   (coe v6) (coe v2)))))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             du_copy_1012
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538 (coe v7) (coe v4))
                                (coe v4))
                             (coe v6) (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538 (coe v7)
                                         (coe v4))
                                      (coe v4))
                                   (coe v6) (coe v2)))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   du_copy_1012
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538 (coe v7)
                                         (coe v4))
                                      (coe v4))
                                   (coe v6) (coe v2))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                C_alloc_992
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe du_szν_776 (coe v7) (coe v4))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_copy_1012
                                            (coe
                                               MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                               (coe
                                                  MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538
                                                  (coe v7) (coe v4))
                                               (coe v4))
                                            (coe v6) (coe v2))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.freeAll
d_freeAll_1116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_MV_900 -> [T_Ev_990]
d_freeAll_1116 ~v0 ~v1 v2 v3 = du_freeAll_1116 v2 v3
du_freeAll_1116 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_MV_900 -> [T_Ev_990]
du_freeAll_1116 v0 v1
  = case coe v1 of
      C_mone_902 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_mpair_908 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_freeAll_1116 (coe v6) (coe v4))
                    (coe du_freeAll_1116 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minl_914 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v5 v6
               -> coe du_freeAll_1116 (coe v5) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_minr_920 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v5 v6
               -> coe du_freeAll_1116 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mbase_924 v3 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_mmu_928 v3 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_μt_194 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_free_994 (coe v3))
                    (coe
                       du_freeAll_1116
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v5) (coe v0))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mct_934 v4
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v5 v6
               -> coe du_freeAll_1116 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mfn_946 v4 v7 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_free_994 (coe v7)) (coe du_freeAll_1116 (coe v4) (coe v9))
      C_mnu_952 v3 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_free_994 (coe v4))
                    (coe
                       du_freeAll_1116
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_Coalg_1538 (coe v6) (coe v3))
                          (coe v3))
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.tag
d_tag_1150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> T_MV_900 -> T_MV_900
d_tag_1150 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_tag_1150 v4 v5
du_tag_1150 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> T_MV_900 -> T_MV_900
du_tag_1150 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe C_mct_934 v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v2 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v2 v3
        -> case coe v1 of
             C_minl_914 v6 -> coe C_minl_914 (coe du_tag_1150 (coe v2) (coe v6))
             C_minr_920 v6 -> coe C_minr_920 (coe du_tag_1150 (coe v3) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> case coe v1 of
             C_mpair_908 v6 v7
               -> coe
                    C_mpair_908 (coe du_tag_1150 (coe v2) (coe v6))
                    (coe du_tag_1150 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.TL
d_TL_1184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) -> ()
d_TL_1184 = erased
-- Once.LinCore.Values.none
d_none_1186 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer -> Integer
d_none_1186 ~v0 ~v1 ~v2 = du_none_1186
du_none_1186 :: Integer
du_none_1186 = coe (0 :: Integer)
-- Once.LinCore.Values.δd
d_δd_1190 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_δd_1190 ~v0 ~v1 ~v2 v3 = du_δd_1190 v3
du_δd_1190 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_δd_1190 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe (1 :: Integer))
             else coe seq (coe v2) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.δn
d_δn_1192 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  Integer -> Integer -> Integer
d_δn_1192 ~v0 ~v1 v2 v3 = du_δn_1192 v2 v3
du_δn_1192 :: Integer -> Integer -> Integer
du_δn_1192 v0 v1
  = coe
      du_δd_1190
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v0) (coe v1))
-- Once.LinCore.Values.tstep
d_tstep_1198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Ev_990 -> (Integer -> Integer) -> Integer -> Integer
d_tstep_1198 ~v0 ~v1 v2 v3 = du_tstep_1198 v2 v3
du_tstep_1198 ::
  T_Ev_990 -> (Integer -> Integer) -> Integer -> Integer
du_tstep_1198 v0 v1
  = case coe v0 of
      C_alloc_992 v2 -> coe v1
      C_free_994 v2 -> coe v1
      C_peek_996 v2 -> coe v1
      C_io_1000 v2 v3 v4 -> coe v1
      C_stp_1004 v2 v3 -> coe v1
      C_tmp_1006 v2
        -> case coe v2 of
             C_tnew_986 v3
               -> coe
                    (\ v4 -> addInt (coe du_δn_1192 (coe v3) (coe v4)) (coe v1 v4))
             C_tdel_988 v3
               -> coe
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (coe v1 v4)
                         (coe du_δn_1192 (coe v3) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Values.tplay
d_tplay_1222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_990] -> (Integer -> Integer) -> Integer -> Integer
d_tplay_1222 ~v0 ~v1 v2 v3 = du_tplay_1222 v2 v3
du_tplay_1222 ::
  [T_Ev_990] -> (Integer -> Integer) -> Integer -> Integer
du_tplay_1222 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldl_230
      (coe (\ v2 v3 -> coe du_tstep_1198 (coe v3) (coe v2))) (coe v1)
      (coe v0)
-- Once.LinCore.Values.tpre
d_tpre_1232 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Ev_990 -> (Integer -> Integer) -> ()
d_tpre_1232 = erased
-- Once.LinCore.Values.TOK
d_TOK_1252 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_990] -> (Integer -> Integer) -> ()
d_TOK_1252 = erased
-- Once.LinCore.Values.TLeg
d_TLeg_1258 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_990] -> ()
d_TLeg_1258 = erased
-- Once.LinCore.Values.TBal
d_TBal_1260 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_Ev_990] -> ()
d_TBal_1260 = erased
-- Once.LinCore.Values.tmps
d_tmps_1268 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [T_TEv_984] -> [T_Ev_990]
d_tmps_1268 ~v0 ~v1 = du_tmps_1268
du_tmps_1268 :: [T_TEv_984] -> [T_Ev_990]
du_tmps_1268
  = coe MAlonzo.Code.Data.List.Base.du_map_22 (coe C_tmp_1006)
