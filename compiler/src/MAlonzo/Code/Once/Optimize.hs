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

module MAlonzo.Code.Once.Optimize where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize.IRHead
d_IRHead_4 = ()
data T_IRHead_4
  = C_h'45'id_6 | C_h'45''8728'_8 | C_h'45''10216''44''10217'_10 |
    C_h'45'fst_12 | C_h'45'snd_14 | C_h'45'inl_16 | C_h'45'inr_18 |
    C_h'45'case_20 | C_h'45'terminal_22 | C_h'45'initial_24 |
    C_h'45'curry_26 | C_h'45'apply_28 | C_h'45'arr_30 | C_h'45'In_32 |
    C_h'45'out'45'μ_34 | C_h'45'Cata_36 | C_h'45'Out_38 |
    C_h'45'in'45'ν_40 | C_h'45'Ana_42 | C_h'45'Iter_44 |
    C_h'45'SigOp_46 | C_h'45'const_48 | C_h'45'Call_50
-- Once.Optimize.headTag
d_headTag_52 :: T_IRHead_4 -> Integer
d_headTag_52 v0
  = case coe v0 of
      C_h'45'id_6 -> coe (0 :: Integer)
      C_h'45''8728'_8 -> coe (1 :: Integer)
      C_h'45''10216''44''10217'_10 -> coe (2 :: Integer)
      C_h'45'fst_12 -> coe (3 :: Integer)
      C_h'45'snd_14 -> coe (4 :: Integer)
      C_h'45'inl_16 -> coe (5 :: Integer)
      C_h'45'inr_18 -> coe (6 :: Integer)
      C_h'45'case_20 -> coe (7 :: Integer)
      C_h'45'terminal_22 -> coe (8 :: Integer)
      C_h'45'initial_24 -> coe (9 :: Integer)
      C_h'45'curry_26 -> coe (10 :: Integer)
      C_h'45'apply_28 -> coe (11 :: Integer)
      C_h'45'arr_30 -> coe (12 :: Integer)
      C_h'45'In_32 -> coe (14 :: Integer)
      C_h'45'out'45'μ_34 -> coe (15 :: Integer)
      C_h'45'Cata_36 -> coe (16 :: Integer)
      C_h'45'Out_38 -> coe (18 :: Integer)
      C_h'45'in'45'ν_40 -> coe (19 :: Integer)
      C_h'45'Ana_42 -> coe (20 :: Integer)
      C_h'45'Iter_44 -> coe (21 :: Integer)
      C_h'45'SigOp_46 -> coe (24 :: Integer)
      C_h'45'const_48 -> coe (25 :: Integer)
      C_h'45'Call_50 -> coe (26 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.headTag-inj
d_headTag'45'inj_58 ::
  T_IRHead_4 ->
  T_IRHead_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headTag'45'inj_58 = erased
-- Once.Optimize._≟IRHead_
d__'8799'IRHead__60 ::
  T_IRHead_4 ->
  T_IRHead_4 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRHead__60 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_headTag_52 (coe v0)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_headTag_52 (coe v0)) (coe d_headTag_52 (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.ir-head
d_ir'45'head_88 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_4
d_ir'45'head_88 ~v0 ~v1 v2 = du_ir'45'head_88 v2
du_ir'45'head_88 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_4
du_ir'45'head_88 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_h'45'id_6
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_h'45''8728'_8
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_h'45''10216''44''10217'_10
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_h'45'fst_12
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_h'45'snd_14
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_h'45'inl_16
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_h'45'inr_18
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_h'45'case_20
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_h'45'terminal_22
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_h'45'initial_24
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_h'45'curry_26
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_h'45'apply_28
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_h'45'In_32
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_h'45'out'45'μ_34
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_h'45'Cata_36
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_h'45'Out_38
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_h'45'in'45'ν_40
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_h'45'Ana_42
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_h'45'Iter_44
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_h'45'const_48
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_h'45'SigOp_46
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_h'45'Call_50
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-Void
d_is'45'Void_92 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_is'45'Void_92 ~v0 v1 = du_is'45'Void_92 v1
du_is'45'Void_92 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
du_is'45'Void_92 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isUnitType
d_isUnitType_96 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_isUnitType_96 ~v0 v1 = du_isUnitType_96 v1
du_isUnitType_96 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
du_isUnitType_96 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isVoidType
d_isVoidType_100 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_isVoidType_100 ~v0 v1 = du_isVoidType_100 v1
du_isVoidType_100 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
du_isVoidType_100 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-fst?
d_is'45'fst'63'_106 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'fst'63'_106 ~v0 ~v1 v2 = du_is'45'fst'63'_106 v2
du_is'45'fst'63'_106 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'fst'63'_106 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
         (coe C_h'45'fst_12))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_114 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'snd'63'_114 ~v0 ~v1 v2 = du_is'45'snd'63'_114 v2
du_is'45'snd'63'_114 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'snd'63'_114 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
         (coe C_h'45'snd_14))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_122 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'terminal'63'_122 ~v0 ~v1 v2 = du_is'45'terminal'63'_122 v2
du_is'45'terminal'63'_122 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'terminal'63'_122 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
         (coe C_h'45'terminal_22))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_134 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_safe'45'pair'45'distrib_134 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_134 v4 v5
du_safe'45'pair'45'distrib_134 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_safe'45'pair'45'distrib_134 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_106 (coe v0))
         (coe du_is'45'snd'63'_114 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_114 (coe v0))
            (coe du_is'45'fst'63'_106 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_122 (coe v0))
            (coe du_is'45'terminal'63'_122 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_144 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_wants'45'coprod_144 ~v0 ~v1 v2 = du_wants'45'coprod_144 v2
du_wants'45'coprod_144 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_wants'45'coprod_144 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
         (coe
            d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
            (coe C_h'45'case_20)))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
         (coe
            d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
            (coe C_h'45'terminal_22)))
-- Once.Optimize.PairView
d_PairView_154 a0 a1 a2 a3 = ()
data T_PairView_154 = C_is'45'pair_166 | C_is'45'other'45'pair_176
-- Once.Optimize.CoprodView
d_CoprodView_184 a0 a1 a2 a3 = ()
data T_CoprodView_184
  = C_is'45'inl_190 | C_is'45'inr_196 | C_is'45'other'45'coprod_206
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_212 a0 a1 a2 = ()
data T_ComposeFirstView_212
  = C_cf'45'id_216 | C_cf'45'terminal_220 | C_cf'45'fst_226 |
    C_cf'45'snd_232 | C_cf'45'case_244 | C_cf'45'other_252
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_258 a0 a1 a2 = ()
data T_ComposeSecondView_258
  = C_cs'45'id_262 | C_cs'45'initial_266 | C_cs'45'other_274
-- Once.Optimize.FstSndView
d_FstSndView_280 a0 a1 a2 = ()
data T_FstSndView_280
  = C_fsv'45'fst_286 | C_fsv'45'snd_292 | C_fsv'45'other_300
-- Once.Optimize.InlInrView
d_InlInrView_306 a0 a1 a2 = ()
data T_InlInrView_306
  = C_iiv'45'inl_312 | C_iiv'45'inr_318 | C_iiv'45'other_326
-- Once.Optimize.pairView-gen
d_pairView'45'gen_340 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_154
d_pairView'45'gen_340 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_340 v2
du_pairView'45'gen_340 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_154
du_pairView'45'gen_340 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'pair_166
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'pair_176
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_is'45'other'45'pair_176
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_432 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_154
d_pairView_432 ~v0 ~v1 ~v2 v3 = du_pairView_432 v3
du_pairView_432 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_154
du_pairView_432 v0 = coe du_pairView'45'gen_340 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_448 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_184
d_coprodView'45'gen_448 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_448 v2
du_coprodView'45'gen_448 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_184
du_coprodView'45'gen_448 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'inl_190
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'inr_196
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_curry_84 v4
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_Out_110 v2
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_Iter_130 v4
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'coprod_206
      MAlonzo.Code.Once.IR.C_Call_146 v3
        -> coe C_is'45'other'45'coprod_206
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_538 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_184
d_coprodView_538 ~v0 ~v1 ~v2 v3 = du_coprodView_538 v3
du_coprodView_538 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_184
du_coprodView_538 v0 = coe du_coprodView'45'gen_448 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_548 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_212
d_composeFirstView_548 ~v0 ~v1 v2 = du_composeFirstView_548 v2
du_composeFirstView_548 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_212
du_composeFirstView_548 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_216
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_226
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_232
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_244
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_220
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cf'45'other_252
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cf'45'other_252
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_596 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_258
d_composeSecondView_596 ~v0 ~v1 v2 = du_composeSecondView_596 v2
du_composeSecondView_596 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_258
du_composeSecondView_596 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_262
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_266
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cs'45'other_274
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cs'45'other_274
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_644 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_280
d_fstSndView_644 ~v0 ~v1 v2 = du_fstSndView_644 v2
du_fstSndView_644 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_280
du_fstSndView_644 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_286
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_292
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_fsv'45'other_300
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_fsv'45'other_300
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_692 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_306
d_inlInrView_692 ~v0 ~v1 v2 = du_inlInrView_692 v2
du_inlInrView_692 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_306
du_inlInrView_692 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_312
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_318
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_iiv'45'other_326
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_iiv'45'other_326
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_738 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_738 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_738 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_738 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_738 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_738 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_738 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_738 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_738
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_In_94 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           d_has'45'effect'63'_738
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v1)))
                           (coe v1) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Ana_122 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           d_has'45'effect'63'_738 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v9))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v6
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_const_134 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_SigOp_140 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_Call_146 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_764 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_764 ~v0 v1 v2 v3
  = du_optimize'45'fst_764 v1 v2 v3
du_optimize'45'fst_764 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'fst_764 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_340 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_166
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v12
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_176
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_fst_42) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_786 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_786 ~v0 v1 v2 v3
  = du_optimize'45'snd_786 v1 v2 v3
du_optimize'45'snd_786 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'snd_786 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_340 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_166
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_176
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_snd_48) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_810 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_810 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_810 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_810 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_810 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_448 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_190 -> coe v2
         C_is'45'inr_196 -> coe v3
         C_is'45'other'45'coprod_206
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_880 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_880 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_880 v1 v3 v4
du_optimize'45'compose'45'second_880 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_880 v0 v1 v2
  = let v3 = coe du_composeSecondView_596 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_262 -> coe v1
         C_cs'45'initial_266 -> coe MAlonzo.Code.Once.IR.C_initial_76
         C_cs'45'other_274
           -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_910 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_910 v0 v1 v2 v3 v4
  = let v5 = d_has'45'effect'63'_738 (coe v0) (coe v1) (coe v4) in
    coe
      (if coe v5
         then coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v3 v4
         else (let v6 = coe du_composeFirstView_548 (coe v3) in
               coe
                 (case coe v6 of
                    C_cf'45'id_216 -> coe v4
                    C_cf'45'terminal_220 -> coe MAlonzo.Code.Once.IR.C_terminal_72
                    C_cf'45'fst_226
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'fst_764 (coe v2) (coe v10) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'snd_232
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'snd_786 (coe v9) (coe v2) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'case_244
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.IR.C_case_68 v17 v18
                                    -> coe
                                         du_optimize'45'post'45'case_810 (coe v12) (coe v13)
                                         (coe v17) (coe v18) (coe v4)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'other_252
                      -> coe
                           du_optimize'45'compose'45'second_880 (coe v1) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_972 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_280 ->
  T_FstSndView_280 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair'45'aux_972 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_972 v3 v4 v5 v6
du_optimize'45'pair'45'aux_972 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_280 ->
  T_FstSndView_280 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair'45'aux_972 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_286
        -> case coe v3 of
             C_fsv'45'fst_286
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_292 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_fsv'45'other_300
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_292
        -> case coe v3 of
             C_fsv'45'fst_286
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_292
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_300
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_300
        -> case coe v3 of
             C_fsv'45'fst_286
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_292
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_300
               -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_1016 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_1016 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_1016 v3 v4
du_optimize'45'pair_1016 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair_1016 v0 v1
  = coe
      du_optimize'45'pair'45'aux_972 (coe v0) (coe v1)
      (coe du_fstSndView_644 (coe v0)) (coe du_fstSndView_644 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_1032 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_306 ->
  T_InlInrView_306 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case'45'aux_1032 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_1032 v3 v4 v5 v6
du_optimize'45'case'45'aux_1032 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_306 ->
  T_InlInrView_306 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case'45'aux_1032 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_312
        -> case coe v3 of
             C_iiv'45'inl_312
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_318 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_iiv'45'other_326
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_318
        -> case coe v3 of
             C_iiv'45'inl_312
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_318
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_326
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_326
        -> case coe v3 of
             C_iiv'45'inl_312
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_318
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_326 -> coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_1076 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_1076 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_1076 v3 v4
du_optimize'45'case_1076 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case_1076 v0 v1
  = coe
      du_optimize'45'case'45'aux_1032 (coe v0) (coe v1)
      (coe du_inlInrView_692 (coe v0)) (coe du_inlInrView_692 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_1086 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_1086 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_910 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1092 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1092 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_optimize'45'pair_1016
                    (coe d_optimize'45'once_1092 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1092 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.IR.C_snd_48 -> coe MAlonzo.Code.Once.IR.C_snd_48
      MAlonzo.Code.Once.IR.C_inl_54
        -> let v5
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                             (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0)))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe
                              eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                    (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_initial_76)
                       else coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_inl_54)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_inr_60
        -> let v5
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                             (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0)))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe
                              eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                    (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_initial_76)
                       else coe seq (coe v7) (coe MAlonzo.Code.Once.IR.C_inr_60)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    du_optimize'45'case_1076
                    (coe d_optimize'45'once_1092 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1092 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Once.IR.C_terminal_72
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Once.IR.C_initial_76
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_84
                    (d_optimize'45'once_1092
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Once.IR.C_apply_90
      MAlonzo.Code.Once.IR.C_In_94 v4
        -> coe MAlonzo.Code.Once.IR.C_In_94 v4
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_106 v4
                           (d_optimize'45'once_1092
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10)
                                    (coe v1)))
                              (coe v1) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4
        -> coe MAlonzo.Code.Once.IR.C_Out_110 v4
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
      MAlonzo.Code.Once.IR.C_Ana_122 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Ana_122 v4
                           (d_optimize'45'once_1092
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v9))
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_Iter_130
                    (d_optimize'45'once_1092
                       (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v8))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_134 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_140 v3 v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                     (coe (0 :: Integer)) (coe v3)
                     (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                       else coe seq (coe v8) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_Call_146 v5
        -> coe MAlonzo.Code.Once.IR.C_Call_146 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_1092 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_1092 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
              (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v1)))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe
                       eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v1))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_irtyTag_198
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                       (coe
                          eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v1))
                          (coe
                             MAlonzo.Code.Once.IRTy.d_irtyTag_198
                             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (let v6
                              = d_has'45'effect'63'_738
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_1086 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
                             else coe MAlonzo.Code.Once.IR.C_terminal_72))
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v6 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                          (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe
                                           eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                              (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                           (coe
                                              eqInt
                                              (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_1086 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_1242 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_1242 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1242 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1092 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1254 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_1254 v0 v1
  = coe d_optimize'45'n_1242 (coe v0) (coe v1) (coe (10 :: Integer))
