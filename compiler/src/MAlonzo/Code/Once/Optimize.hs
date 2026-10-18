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
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
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
    C_h'45'in'45'ν_40 | C_h'45'Ana_42 | C_h'45'SigOp_44 |
    C_h'45'const_46 | C_h'45'Call_48
-- Once.Optimize.headTag
d_headTag_50 :: T_IRHead_4 -> Integer
d_headTag_50 v0
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
      C_h'45'SigOp_44 -> coe (24 :: Integer)
      C_h'45'const_46 -> coe (25 :: Integer)
      C_h'45'Call_48 -> coe (26 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.headTag-inj
d_headTag'45'inj_56 ::
  T_IRHead_4 ->
  T_IRHead_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_headTag'45'inj_56 = erased
-- Once.Optimize._≟IRHead_
d__'8799'IRHead__58 ::
  T_IRHead_4 ->
  T_IRHead_4 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRHead__58 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe d_headTag_50 (coe v0)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe d_headTag_50 (coe v0)) (coe d_headTag_50 (coe v1)))) in
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
d_ir'45'head_86 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_4
d_ir'45'head_86 ~v0 ~v1 v2 = du_ir'45'head_86 v2
du_ir'45'head_86 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_4
du_ir'45'head_86 v0
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
      MAlonzo.Code.Once.IR.C_const_126 v2 v3 -> coe C_h'45'const_46
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3 -> coe C_h'45'SigOp_44
      MAlonzo.Code.Once.IR.C_Call_138 v3 -> coe C_h'45'Call_48
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-Void
d_is'45'Void_88 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Bool
d_is'45'Void_88 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isUnitType
d_isUnitType_90 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Bool
d_isUnitType_90 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isVoidType
d_isVoidType_92 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Bool
d_isVoidType_92 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-fst?
d_is'45'fst'63'_98 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'fst'63'_98 ~v0 ~v1 v2 = du_is'45'fst'63'_98 v2
du_is'45'fst'63'_98 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'fst'63'_98 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__58 (coe du_ir'45'head_86 (coe v0))
         (coe C_h'45'fst_12))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_106 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'snd'63'_106 ~v0 ~v1 v2 = du_is'45'snd'63'_106 v2
du_is'45'snd'63'_106 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'snd'63'_106 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__58 (coe du_ir'45'head_86 (coe v0))
         (coe C_h'45'snd_14))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_114 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'terminal'63'_114 ~v0 ~v1 v2 = du_is'45'terminal'63'_114 v2
du_is'45'terminal'63'_114 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'terminal'63'_114 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__58 (coe du_ir'45'head_86 (coe v0))
         (coe C_h'45'terminal_22))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_126 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_safe'45'pair'45'distrib_126 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_126 v4 v5
du_safe'45'pair'45'distrib_126 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_safe'45'pair'45'distrib_126 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_98 (coe v0))
         (coe du_is'45'snd'63'_106 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_106 (coe v0))
            (coe du_is'45'fst'63'_98 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_114 (coe v0))
            (coe du_is'45'terminal'63'_114 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_136 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_wants'45'coprod_136 ~v0 ~v1 v2 = du_wants'45'coprod_136 v2
du_wants'45'coprod_136 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_wants'45'coprod_136 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
         (coe
            d__'8799'IRHead__58 (coe du_ir'45'head_86 (coe v0))
            (coe C_h'45'case_20)))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
         (coe
            d__'8799'IRHead__58 (coe du_ir'45'head_86 (coe v0))
            (coe C_h'45'terminal_22)))
-- Once.Optimize.PairView
d_PairView_146 a0 a1 a2 a3 = ()
data T_PairView_146 = C_is'45'pair_158 | C_is'45'other'45'pair_168
-- Once.Optimize.CoprodView
d_CoprodView_176 a0 a1 a2 a3 = ()
data T_CoprodView_176
  = C_is'45'inl_182 | C_is'45'inr_188 | C_is'45'other'45'coprod_198
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_204 a0 a1 a2 = ()
data T_ComposeFirstView_204
  = C_cf'45'id_208 | C_cf'45'terminal_212 | C_cf'45'fst_218 |
    C_cf'45'snd_224 | C_cf'45'case_236 | C_cf'45'other_244
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_250 a0 a1 a2 = ()
data T_ComposeSecondView_250
  = C_cs'45'id_254 | C_cs'45'initial_258 | C_cs'45'other_266
-- Once.Optimize.FstSndView
d_FstSndView_272 a0 a1 a2 = ()
data T_FstSndView_272
  = C_fsv'45'fst_278 | C_fsv'45'snd_284 | C_fsv'45'other_292
-- Once.Optimize.InlInrView
d_InlInrView_298 a0 a1 a2 = ()
data T_InlInrView_298
  = C_iiv'45'inl_304 | C_iiv'45'inr_310 | C_iiv'45'other_318
-- Once.Optimize.pairView-gen
d_pairView'45'gen_332 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_146
d_pairView'45'gen_332 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_332 v2
du_pairView'45'gen_332 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_146
du_pairView'45'gen_332 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'pair_158
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_const_126 v2 v3
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3
        -> coe C_is'45'other'45'pair_168
      MAlonzo.Code.Once.IR.C_Call_138 v3 -> coe C_is'45'other'45'pair_168
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_420 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_146
d_pairView_420 ~v0 ~v1 ~v2 v3 = du_pairView_420 v3
du_pairView_420 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_146
du_pairView_420 v0 = coe du_pairView'45'gen_332 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_436 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_176
d_coprodView'45'gen_436 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_436 v2
du_coprodView'45'gen_436 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_176
du_coprodView'45'gen_436 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'inl_182
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'inr_188
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_curry_84 v4
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_Out_110 v2
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_const_126 v2 v3
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3
        -> coe C_is'45'other'45'coprod_198
      MAlonzo.Code.Once.IR.C_Call_138 v3
        -> coe C_is'45'other'45'coprod_198
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_522 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_176
d_coprodView_522 ~v0 ~v1 ~v2 v3 = du_coprodView_522 v3
du_coprodView_522 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_176
du_coprodView_522 v0 = coe du_coprodView'45'gen_436 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_532 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_204
d_composeFirstView_532 ~v0 ~v1 v2 = du_composeFirstView_532 v2
du_composeFirstView_532 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_204
du_composeFirstView_532 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_208
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_218
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_224
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_236
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_212
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_const_126 v2 v3 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3 -> coe C_cf'45'other_244
      MAlonzo.Code.Once.IR.C_Call_138 v3 -> coe C_cf'45'other_244
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_578 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_250
d_composeSecondView_578 ~v0 ~v1 v2 = du_composeSecondView_578 v2
du_composeSecondView_578 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_250
du_composeSecondView_578 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_254
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_258
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_const_126 v2 v3 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3 -> coe C_cs'45'other_266
      MAlonzo.Code.Once.IR.C_Call_138 v3 -> coe C_cs'45'other_266
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_624 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_272
d_fstSndView_624 ~v0 ~v1 v2 = du_fstSndView_624 v2
du_fstSndView_624 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_272
du_fstSndView_624 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_278
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_284
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_const_126 v2 v3 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3 -> coe C_fsv'45'other_292
      MAlonzo.Code.Once.IR.C_Call_138 v3 -> coe C_fsv'45'other_292
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_670 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_298
d_inlInrView_670 ~v0 ~v1 v2 = du_inlInrView_670 v2
du_inlInrView_670 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_298
du_inlInrView_670 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_304
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_310
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_const_126 v2 v3 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_SigOp_132 v1 v2 v3 -> coe C_iiv'45'other_318
      MAlonzo.Code.Once.IR.C_Call_138 v3 -> coe C_iiv'45'other_318
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_714 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_714 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_714 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_714 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_714 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_714 (coe v0) (coe v9) (coe v7))
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
                    (coe d_has'45'effect'63'_714 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_714 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_714
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
                           d_has'45'effect'63'_714
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v1)))
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
                           d_has'45'effect'63'_714 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v9))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_126 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_SigOp_132 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_Call_138 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_740 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_740 ~v0 v1 v2 v3
  = du_optimize'45'fst_740 v1 v2 v3
du_optimize'45'fst_740 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'fst_740 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_332 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_158
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v12
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_168
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_fst_42) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_762 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_762 ~v0 v1 v2 v3
  = du_optimize'45'snd_762 v1 v2 v3
du_optimize'45'snd_762 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'snd_762 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_332 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_158
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_168
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_snd_48) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_786 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_786 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_786 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_786 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_786 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_436 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_182 -> coe v2
         C_is'45'inr_188 -> coe v3
         C_is'45'other'45'coprod_198
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_856 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_856 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_856 v1 v3 v4
du_optimize'45'compose'45'second_856 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_856 v0 v1 v2
  = let v3 = coe du_composeSecondView_578 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_254 -> coe v1
         C_cs'45'initial_258 -> coe MAlonzo.Code.Once.IR.C_initial_76
         C_cs'45'other_266
           -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_886 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_886 v0 v1 v2 v3 v4
  = let v5 = d_has'45'effect'63'_714 (coe v0) (coe v1) (coe v4) in
    coe
      (if coe v5
         then coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v3 v4
         else (let v6 = coe du_composeFirstView_532 (coe v3) in
               coe
                 (case coe v6 of
                    C_cf'45'id_208 -> coe v4
                    C_cf'45'terminal_212 -> coe MAlonzo.Code.Once.IR.C_terminal_72
                    C_cf'45'fst_218
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'fst_740 (coe v2) (coe v10) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'snd_224
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'snd_762 (coe v9) (coe v2) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'case_236
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.IR.C_case_68 v17 v18
                                    -> coe
                                         du_optimize'45'post'45'case_786 (coe v12) (coe v13)
                                         (coe v17) (coe v18) (coe v4)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'other_244
                      -> coe
                           du_optimize'45'compose'45'second_856 (coe v1) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_948 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_272 ->
  T_FstSndView_272 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair'45'aux_948 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_948 v3 v4 v5 v6
du_optimize'45'pair'45'aux_948 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_272 ->
  T_FstSndView_272 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair'45'aux_948 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_278
        -> case coe v3 of
             C_fsv'45'fst_278
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_284 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_fsv'45'other_292
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_284
        -> case coe v3 of
             C_fsv'45'fst_278
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_284
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_292
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_292
        -> case coe v3 of
             C_fsv'45'fst_278
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_284
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_292
               -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_992 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_992 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_992 v3 v4
du_optimize'45'pair_992 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair_992 v0 v1
  = coe
      du_optimize'45'pair'45'aux_948 (coe v0) (coe v1)
      (coe du_fstSndView_624 (coe v0)) (coe du_fstSndView_624 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_1008 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_298 ->
  T_InlInrView_298 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case'45'aux_1008 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_1008 v3 v4 v5 v6
du_optimize'45'case'45'aux_1008 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_298 ->
  T_InlInrView_298 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case'45'aux_1008 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_304
        -> case coe v3 of
             C_iiv'45'inl_304
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_310 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_iiv'45'other_318
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_310
        -> case coe v3 of
             C_iiv'45'inl_304
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_310
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_318
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_318
        -> case coe v3 of
             C_iiv'45'inl_304
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_310
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_318 -> coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_1052 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_1052 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_1052 v3 v4
du_optimize'45'case_1052 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case_1052 v0 v1
  = coe
      du_optimize'45'case'45'aux_1008 (coe v0) (coe v1)
      (coe du_inlInrView_670 (coe v0)) (coe du_inlInrView_670 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_1062 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_1062 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_886 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1068 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1068 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_optimize'45'pair_992
                    (coe d_optimize'45'once_1068 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1068 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.IR.C_snd_48 -> coe MAlonzo.Code.Once.IR.C_snd_48
      MAlonzo.Code.Once.IR.C_inl_54
        -> let v5
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_202
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                             (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0)))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe
                              eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_irtyTag_194
                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_irtyTag_194
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
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_202
                     (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                             (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0)))
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                           (coe
                              eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_irtyTag_194
                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                           (coe
                              MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                              (coe
                                 eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_irtyTag_194
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
                    du_optimize'45'case_1052
                    (coe d_optimize'45'once_1068 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1068 (coe v9) (coe v1) (coe v7))
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
                    (d_optimize'45'once_1068
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
                           (d_optimize'45'once_1068
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
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
                           (d_optimize'45'once_1068
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v9))
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_126 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_126 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_132 v3 v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
                     (coe v3) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                       else coe seq (coe v8) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_Call_138 v5
        -> coe MAlonzo.Code.Once.IR.C_Call_138 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_1068 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_1068 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_202
              (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v1)))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe
                       eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v1))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_irtyTag_194
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                       (coe
                          eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v1))
                          (coe
                             MAlonzo.Code.Once.IRTy.d_irtyTag_194
                             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (let v6
                              = d_has'45'effect'63'_714
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_1062 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
                             else coe MAlonzo.Code.Once.IR.C_terminal_72))
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_202
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v6 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                          (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe
                                           eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_irtyTag_194
                                              (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                           (coe
                                              eqInt
                                              (coe MAlonzo.Code.Once.IRTy.d_irtyTag_194 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_irtyTag_194
                                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_1062 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_1216 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_1216 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1216 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1068 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1228 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_1228 v0 v1
  = coe d_optimize'45'n_1216 (coe v0) (coe v1) (coe (10 :: Integer))
