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
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
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
d_is'45'Void_90 :: MAlonzo.Code.Once.Internal.Type.T_Type_8 -> Bool
d_is'45'Void_90 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isUnitType
d_isUnitType_92 :: MAlonzo.Code.Once.Internal.Type.T_Type_8 -> Bool
d_isUnitType_92 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isVoidType
d_isVoidType_94 :: MAlonzo.Code.Once.Internal.Type.T_Type_8 -> Bool
d_isVoidType_94 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Int_34
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_Float_36
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Internal.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-fst?
d_is'45'fst'63'_100 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'fst'63'_100 ~v0 ~v1 v2 = du_is'45'fst'63'_100 v2
du_is'45'fst'63'_100 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'fst'63'_100 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
         (coe C_h'45'fst_12))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_108 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'snd'63'_108 ~v0 ~v1 v2 = du_is'45'snd'63'_108 v2
du_is'45'snd'63'_108 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'snd'63'_108 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
         (coe C_h'45'snd_14))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_116 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'terminal'63'_116 ~v0 ~v1 v2 = du_is'45'terminal'63'_116 v2
du_is'45'terminal'63'_116 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'terminal'63'_116 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         d__'8799'IRHead__60 (coe du_ir'45'head_88 (coe v0))
         (coe C_h'45'terminal_22))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_128 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_safe'45'pair'45'distrib_128 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_128 v4 v5
du_safe'45'pair'45'distrib_128 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_safe'45'pair'45'distrib_128 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_100 (coe v0))
         (coe du_is'45'snd'63'_108 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_108 (coe v0))
            (coe du_is'45'fst'63'_100 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_116 (coe v0))
            (coe du_is'45'terminal'63'_116 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_138 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_wants'45'coprod_138 ~v0 ~v1 v2 = du_wants'45'coprod_138 v2
du_wants'45'coprod_138 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_wants'45'coprod_138 v0
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
d_PairView_148 a0 a1 a2 a3 = ()
data T_PairView_148 = C_is'45'pair_160 | C_is'45'other'45'pair_170
-- Once.Optimize.CoprodView
d_CoprodView_178 a0 a1 a2 a3 = ()
data T_CoprodView_178
  = C_is'45'inl_184 | C_is'45'inr_190 | C_is'45'other'45'coprod_200
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_206 a0 a1 a2 = ()
data T_ComposeFirstView_206
  = C_cf'45'id_210 | C_cf'45'terminal_214 | C_cf'45'fst_220 |
    C_cf'45'snd_226 | C_cf'45'case_238 | C_cf'45'other_246
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_252 a0 a1 a2 = ()
data T_ComposeSecondView_252
  = C_cs'45'id_256 | C_cs'45'initial_260 | C_cs'45'other_268
-- Once.Optimize.FstSndView
d_FstSndView_274 a0 a1 a2 = ()
data T_FstSndView_274
  = C_fsv'45'fst_280 | C_fsv'45'snd_286 | C_fsv'45'other_294
-- Once.Optimize.InlInrView
d_InlInrView_300 a0 a1 a2 = ()
data T_InlInrView_300
  = C_iiv'45'inl_306 | C_iiv'45'inr_312 | C_iiv'45'other_320
-- Once.Optimize.pairView-gen
d_pairView'45'gen_334 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_148
d_pairView'45'gen_334 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_334 v2
du_pairView'45'gen_334 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_148
du_pairView'45'gen_334 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'pair_160
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'pair_170
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_is'45'other'45'pair_170
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_426 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_148
d_pairView_426 ~v0 ~v1 ~v2 v3 = du_pairView_426 v3
du_pairView_426 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_148
du_pairView_426 v0 = coe du_pairView'45'gen_334 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_442 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_178
d_coprodView'45'gen_442 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_442 v2
du_coprodView'45'gen_442 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_178
du_coprodView'45'gen_442 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'inl_184
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'inr_190
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_curry_84 v4
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_Out_110 v2
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_Iter_130 v4
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'coprod_200
      MAlonzo.Code.Once.IR.C_Call_146 v3
        -> coe C_is'45'other'45'coprod_200
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_532 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_178
d_coprodView_532 ~v0 ~v1 ~v2 v3 = du_coprodView_532 v3
du_coprodView_532 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_178
du_coprodView_532 v0 = coe du_coprodView'45'gen_442 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_542 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_206
d_composeFirstView_542 ~v0 ~v1 v2 = du_composeFirstView_542 v2
du_composeFirstView_542 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_206
du_composeFirstView_542 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_210
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_220
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_226
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_238
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_214
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cf'45'other_246
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cf'45'other_246
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_590 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_252
d_composeSecondView_590 ~v0 ~v1 v2 = du_composeSecondView_590 v2
du_composeSecondView_590 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_252
du_composeSecondView_590 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_256
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_260
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cs'45'other_268
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cs'45'other_268
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_638 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_274
d_fstSndView_638 ~v0 ~v1 v2 = du_fstSndView_638 v2
du_fstSndView_638 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_274
du_fstSndView_638 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_280
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_286
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_fsv'45'other_294
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_fsv'45'other_294
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_686 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_300
d_inlInrView_686 ~v0 ~v1 v2 = du_inlInrView_686 v2
du_inlInrView_686 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_300
du_inlInrView_686 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_306
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_312
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_iiv'45'other_320
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_iiv'45'other_320
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_732 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_732 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_732 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_732 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_732 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_732 (coe v0) (coe v9) (coe v7))
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
                    (coe d_has'45'effect'63'_732 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_732 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_732
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
                           d_has'45'effect'63'_732
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
                           d_has'45'effect'63'_732 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v9))
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
d_optimize'45'fst_758 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_758 ~v0 v1 v2 v3
  = du_optimize'45'fst_758 v1 v2 v3
du_optimize'45'fst_758 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'fst_758 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_334 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_160
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v12
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_170
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_fst_42) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_780 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_780 ~v0 v1 v2 v3
  = du_optimize'45'snd_780 v1 v2 v3
du_optimize'45'snd_780 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'snd_780 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_334 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_160
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_170
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_snd_48) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_804 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_804 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_804 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_804 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_804 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_442 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_184 -> coe v2
         C_is'45'inr_190 -> coe v3
         C_is'45'other'45'coprod_200
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_874 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_874 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_874 v1 v3 v4
du_optimize'45'compose'45'second_874 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_874 v0 v1 v2
  = let v3 = coe du_composeSecondView_590 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_256 -> coe v1
         C_cs'45'initial_260 -> coe MAlonzo.Code.Once.IR.C_initial_76
         C_cs'45'other_268
           -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_904 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_904 v0 v1 v2 v3 v4
  = let v5 = d_has'45'effect'63'_732 (coe v0) (coe v1) (coe v4) in
    coe
      (if coe v5
         then coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v3 v4
         else (let v6 = coe du_composeFirstView_542 (coe v3) in
               coe
                 (case coe v6 of
                    C_cf'45'id_210 -> coe v4
                    C_cf'45'terminal_214 -> coe MAlonzo.Code.Once.IR.C_terminal_72
                    C_cf'45'fst_220
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'fst_758 (coe v2) (coe v10) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'snd_226
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'snd_780 (coe v9) (coe v2) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'case_238
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.IR.C_case_68 v17 v18
                                    -> coe
                                         du_optimize'45'post'45'case_804 (coe v12) (coe v13)
                                         (coe v17) (coe v18) (coe v4)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'other_246
                      -> coe
                           du_optimize'45'compose'45'second_874 (coe v1) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_966 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_274 ->
  T_FstSndView_274 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair'45'aux_966 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_966 v3 v4 v5 v6
du_optimize'45'pair'45'aux_966 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_274 ->
  T_FstSndView_274 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair'45'aux_966 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_280
        -> case coe v3 of
             C_fsv'45'fst_280
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_286 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_fsv'45'other_294
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_286
        -> case coe v3 of
             C_fsv'45'fst_280
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_286
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_294
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_294
        -> case coe v3 of
             C_fsv'45'fst_280
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_286
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_294
               -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_1010 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_1010 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_1010 v3 v4
du_optimize'45'pair_1010 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair_1010 v0 v1
  = coe
      du_optimize'45'pair'45'aux_966 (coe v0) (coe v1)
      (coe du_fstSndView_638 (coe v0)) (coe du_fstSndView_638 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_1026 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_300 ->
  T_InlInrView_300 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case'45'aux_1026 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_1026 v3 v4 v5 v6
du_optimize'45'case'45'aux_1026 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_300 ->
  T_InlInrView_300 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case'45'aux_1026 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_306
        -> case coe v3 of
             C_iiv'45'inl_306
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_312 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_iiv'45'other_320
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_312
        -> case coe v3 of
             C_iiv'45'inl_306
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_312
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_320
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_320
        -> case coe v3 of
             C_iiv'45'inl_306
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_312
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_320 -> coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_1070 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_1070 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_1070 v3 v4
du_optimize'45'case_1070 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case_1070 v0 v1
  = coe
      du_optimize'45'case'45'aux_1026 (coe v0) (coe v1)
      (coe du_inlInrView_686 (coe v0)) (coe du_inlInrView_686 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_1080 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_1080 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_904 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1086 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1086 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_optimize'45'pair_1010
                    (coe d_optimize'45'once_1086 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1086 (coe v0) (coe v9) (coe v7))
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
                    du_optimize'45'case_1070
                    (coe d_optimize'45'once_1086 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1086 (coe v9) (coe v1) (coe v7))
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
                    (d_optimize'45'once_1086
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
                           (d_optimize'45'once_1086
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
                           (d_optimize'45'once_1086
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10) (coe v9))
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_Iter_130
                    (d_optimize'45'once_1086
                       (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v8))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_134 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_140 v3 v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216
                     (coe v3) (coe MAlonzo.Code.Once.Internal.Type.C_Void_22) in
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
d_optimize'45'once_1086 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_1086 v0 v1 v2
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
                              = d_has'45'effect'63'_732
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_1080 (coe v0)
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
                                              d_optimize'45'once'45'structural_1080 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_1236 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_1236 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1236 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1086 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1248 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_1248 v0 v1
  = coe d_optimize'45'n_1236 (coe v0) (coe v1) (coe (10 :: Integer))
