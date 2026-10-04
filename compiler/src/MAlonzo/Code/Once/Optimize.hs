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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
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
d__'8799'IRHead__62 ::
  T_IRHead_4 ->
  T_IRHead_4 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRHead__62 v0 v1
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
d_ir'45'head_90 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_4
d_ir'45'head_90 ~v0 ~v1 v2 = du_ir'45'head_90 v2
du_ir'45'head_90 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_IRHead_4
du_ir'45'head_90 v0
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
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4 -> coe C_h'45'Ana_42
      MAlonzo.Code.Once.IR.C_const_124 v2 v3 -> coe C_h'45'const_46
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3 -> coe C_h'45'SigOp_44
      MAlonzo.Code.Once.IR.C_Call_136 v3 -> coe C_h'45'Call_48
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.HeadView
d_HeadView_96 a0 a1 a2 a3 = ()
data T_HeadView_96
  = C_hv'45'id_100 | C_hv'45''8728'_112 |
    C_hv'45''10216''44''10217'_124 | C_hv'45'fst_130 |
    C_hv'45'snd_136 | C_hv'45'inl_142 | C_hv'45'inr_148 |
    C_hv'45'case_160 | C_hv'45'terminal_164 | C_hv'45'initial_168 |
    C_hv'45'curry_178 | C_hv'45'apply_184 | C_hv'45'In_190 |
    C_hv'45'out'45'μ_196 | C_hv'45'Cata_208 | C_hv'45'Out_214 |
    C_hv'45'in'45'ν_220 | C_hv'45'Ana_230 | C_hv'45'SigOp_238 |
    C_hv'45'const_246 | C_hv'45'Call_254
-- Once.Optimize.headView
d_headView_262 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_HeadView_96
d_headView_262 ~v0 ~v1 v2 = du_headView_262 v2
du_headView_262 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_HeadView_96
du_headView_262 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_hv'45'id_100
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_hv'45''8728'_112
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_hv'45''10216''44''10217'_124
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_hv'45'fst_130
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_hv'45'snd_136
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_hv'45'inl_142
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_hv'45'inr_148
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_hv'45'case_160
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_hv'45'terminal_164
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_hv'45'initial_168
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_hv'45'curry_178
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_hv'45'apply_184
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_hv'45'In_190
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_hv'45'out'45'μ_196
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_hv'45'Cata_208
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_hv'45'Out_214
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_hv'45'in'45'ν_220
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4 -> coe C_hv'45'Ana_230
      MAlonzo.Code.Once.IR.C_const_124 v2 v3 -> coe C_hv'45'const_246
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3 -> coe C_hv'45'SigOp_238
      MAlonzo.Code.Once.IR.C_Call_136 v3 -> coe C_hv'45'Call_254
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.subst₂-IR
d_subst'8322''45'IR_272 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_subst'8322''45'IR_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_subst'8322''45'IR_272 v6
du_subst'8322''45'IR_272 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_subst'8322''45'IR_272 v0 = coe v0
-- Once.Optimize.uipK
d_uipK_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uipK_288 = erased
-- Once.Optimize.sigop-dom
d_sigop'45'dom_294 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_sigop'45'dom_294 ~v0 ~v1 v2 = du_sigop'45'dom_294 v2
du_sigop'45'dom_294 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
du_sigop'45'dom_294 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IR.C_SigOp_130 v2 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         _ -> coe v1)
-- Once.Optimize.sigop-cod
d_sigop'45'cod_304 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_sigop'45'cod_304 ~v0 ~v1 v2 = du_sigop'45'cod_304 v2
du_sigop'45'cod_304 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
du_sigop'45'cod_304 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.IR.C_SigOp_130 v2 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
         _ -> coe v1)
-- Once.Optimize.sigop-dom-subst
d_sigop'45'dom'45'subst_324 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'dom'45'subst_324 = erased
-- Once.Optimize.sigop-cod-subst
d_sigop'45'cod'45'subst_342 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigop'45'cod'45'subst_342 = erased
-- Once.Optimize.ir-head-subst₂
d_ir'45'head'45'subst'8322'_360 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'45'head'45'subst'8322'_360 = erased
-- Once.Optimize.head-mismatch-abs
d_head'45'mismatch'45'abs_378 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_head'45'mismatch'45'abs_378 = erased
-- Once.Optimize.cross-no
d_cross'45'no_408 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cross'45'no_408 = erased
-- Once.Optimize.≟IRH
d_'8799'IRH_436 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH_436 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_'8799'IRH_436 v0 v1 v2 v3 v4 v5
du_'8799'IRH_436 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH_436 v0 v1 v2 v3 v4 v5
  = coe
      du_'8799'IRH'45'aux_490 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe
         d__'8799'IRHead__62 (coe du_ir'45'head_90 (coe v4))
         (coe du_ir'45'head_90 (coe v5)))
-- Once.Optimize.≟IRH-diag
d_'8799'IRH'45'diag_454 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'diag_454 v0 v1 v2 v3 v4 v5 ~v6
  = du_'8799'IRH'45'diag_454 v0 v1 v2 v3 v4 v5
du_'8799'IRH'45'diag_454 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'diag_454 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_'8799'IRH'45'on_472 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe du_headView_262 (coe v5))
-- Once.Optimize.≟IRH-on
d_'8799'IRH'45'on_472 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_HeadView_96 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'on_472 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_'8799'IRH'45'on_472 v0 v1 v2 v3 v4 v5 v6
du_'8799'IRH'45'on_472 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_HeadView_96 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'on_472 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C__'8728'__28 v8 v10 v11
        -> coe
             seq (coe v6)
             (case coe v5 of
                MAlonzo.Code.Once.IR.C__'8728'__28 v13 v15 v16
                  -> coe
                       du_'8799'IRH'45''8728''45'aux_650 (coe v0) (coe v8) (coe v1)
                       (coe v10) (coe v11) (coe v15) (coe v16)
                       (coe MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v8) (coe v13))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> coe
                    seq (coe v6)
                    (case coe v5 of
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v17 v18
                         -> coe
                              du_'8799'IRH'45''10216''44''10217''45'aux_686
                              (coe
                                 du_'8799'IRH_436 (coe v0) (coe v12) (coe v0) (coe v12) (coe v10)
                                 (coe v17))
                              (coe
                                 du_'8799'IRH_436 (coe v0) (coe v13) (coe v0) (coe v13) (coe v11)
                                 (coe v18))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_case_68 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
               -> coe
                    seq (coe v6)
                    (case coe v5 of
                       MAlonzo.Code.Once.IR.C_case_68 v17 v18
                         -> coe
                              du_'8799'IRH'45'case'45'aux_746
                              (coe
                                 du_'8799'IRH_436 (coe v12) (coe v1) (coe v12) (coe v1) (coe v10)
                                 (coe v17))
                              (coe
                                 du_'8799'IRH_436 (coe v13) (coe v1) (coe v13) (coe v1) (coe v11)
                                 (coe v18))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_curry_84 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
               -> coe
                    seq (coe v6)
                    (case coe v5 of
                       MAlonzo.Code.Once.IR.C_curry_84 v16
                         -> coe
                              du_'8799'IRH'45'curry'45'aux_802
                              (coe
                                 du_'8799'IRH_436
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v11))
                                 (coe v12)
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v11))
                                 (coe v12) (coe v10) (coe v16))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      MAlonzo.Code.Once.IR.C_In_94 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    seq (coe v6)
                    (case coe v3 of
                       MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                         -> let v11
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__218 (coe v9) (coe v10) in
                            coe
                              (case coe v11 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                   -> if coe v12
                                        then coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                         -> let v11
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__218 (coe v9) (coe v10) in
                            coe
                              (case coe v11 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                   -> if coe v12
                                        then coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v8 v11
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                      -> coe
                           seq (coe v6)
                           (case coe v2 of
                              MAlonzo.Code.Once.IRTy.C__'42'__20 v15 v16
                                -> case coe v16 of
                                     MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
                                       -> case coe v5 of
                                            MAlonzo.Code.Once.IR.C_Cata_106 v19 v22
                                              -> let v23
                                                       = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__218
                                                           (coe v14) (coe v17) in
                                                 coe
                                                   (case coe v23 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                        -> if coe v24
                                                             then coe
                                                                    seq (coe v25)
                                                                    (let v26
                                                                           = coe
                                                                               du_'8799'IRH'45'aux_490
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                                  (coe v12)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                                     (coe v14)
                                                                                     (coe v1)))
                                                                               (coe v1)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.IRTy.C__'42'__20
                                                                                  (coe v12)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                                     (coe v14)
                                                                                     (coe v1)))
                                                                               (coe v1) (coe v11)
                                                                               (coe v22)
                                                                               (let v26
                                                                                      = coe
                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                          erased
                                                                                          (\ v26 ->
                                                                                             coe
                                                                                               MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                               (coe
                                                                                                  d_headTag_50
                                                                                                  (coe
                                                                                                     du_ir'45'head_90
                                                                                                     (coe
                                                                                                        v11))))
                                                                                          (coe
                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                             (coe
                                                                                                eqInt
                                                                                                (coe
                                                                                                   d_headTag_50
                                                                                                   (coe
                                                                                                      du_ir'45'head_90
                                                                                                      (coe
                                                                                                         v11)))
                                                                                                (coe
                                                                                                   d_headTag_50
                                                                                                   (coe
                                                                                                      du_ir'45'head_90
                                                                                                      (coe
                                                                                                         v22))))
                                                                                             (coe
                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                                                (coe
                                                                                                   eqInt
                                                                                                   (coe
                                                                                                      d_headTag_50
                                                                                                      (coe
                                                                                                         du_ir'45'head_90
                                                                                                         (coe
                                                                                                            v11)))
                                                                                                   (coe
                                                                                                      d_headTag_50
                                                                                                      (coe
                                                                                                         du_ir'45'head_90
                                                                                                         (coe
                                                                                                            v22)))))) in
                                                                                coe
                                                                                  (case coe v26 of
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                       -> if coe v27
                                                                                            then coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v28)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                      (coe
                                                                                                         v27)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                         erased))
                                                                                            else coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v28)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                      (coe
                                                                                                         v27)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                                     coe
                                                                       (case coe v26 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                            -> if coe v27
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v28)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v27)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                              erased))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v28)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v27)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             else coe
                                                                    seq (coe v25)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                       (coe v24)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                         -> let v11
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__218 (coe v9) (coe v10) in
                            coe
                              (case coe v11 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                   -> if coe v12
                                        then coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    seq (coe v6)
                    (case coe v3 of
                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                         -> let v11
                                  = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__218 (coe v9) (coe v10) in
                            coe
                              (case coe v11 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                   -> if coe v12
                                        then coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                     erased))
                                        else coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_120 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
               -> coe
                    seq (coe v6)
                    (case coe v3 of
                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                         -> case coe v5 of
                              MAlonzo.Code.Once.IR.C_Ana_120 v14 v16
                                -> let v17
                                         = MAlonzo.Code.Once.IRTy.d__'8799'IRFun__218
                                             (coe v11) (coe v12) in
                                   coe
                                     (case coe v17 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                          -> if coe v18
                                               then coe
                                                      seq (coe v19)
                                                      (let v20
                                                             = coe
                                                                 du_'8799'IRH'45'aux_490 (coe v0)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                    (coe v11) (coe v0))
                                                                 (coe v0)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                    (coe v11) (coe v0))
                                                                 (coe v10) (coe v16)
                                                                 (let v20
                                                                        = coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                            erased
                                                                            (\ v20 ->
                                                                               coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                 (coe
                                                                                    d_headTag_50
                                                                                    (coe
                                                                                       du_ir'45'head_90
                                                                                       (coe v10))))
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                               (coe
                                                                                  eqInt
                                                                                  (coe
                                                                                     d_headTag_50
                                                                                     (coe
                                                                                        du_ir'45'head_90
                                                                                        (coe v10)))
                                                                                  (coe
                                                                                     d_headTag_50
                                                                                     (coe
                                                                                        du_ir'45'head_90
                                                                                        (coe v16))))
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                                  (coe
                                                                                     eqInt
                                                                                     (coe
                                                                                        d_headTag_50
                                                                                        (coe
                                                                                           du_ir'45'head_90
                                                                                           (coe
                                                                                              v10)))
                                                                                     (coe
                                                                                        d_headTag_50
                                                                                        (coe
                                                                                           du_ir'45'head_90
                                                                                           (coe
                                                                                              v16)))))) in
                                                                  coe
                                                                    (case coe v20 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                         -> if coe v21
                                                                              then coe
                                                                                     seq (coe v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                           erased))
                                                                              else coe
                                                                                     seq (coe v22)
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                       coe
                                                         (case coe v20 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                              -> if coe v21
                                                                   then coe
                                                                          seq (coe v22)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v21)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                erased))
                                                                   else coe
                                                                          seq (coe v22)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v21)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               else coe
                                                      seq (coe v19)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v18)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v8 v9
        -> coe
             seq (coe v6)
             (case coe v5 of
                MAlonzo.Code.Once.IR.C_const_124 v11 v12
                  -> coe
                       d_'8799'const'45'irrelevant_1514 v1 v8 v9 v11 v12 v8 v11 v9 v12
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_SigOp_130 v7 v8 v9
        -> coe
             seq (coe v6)
             (case coe v5 of
                MAlonzo.Code.Once.IR.C_SigOp_130 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
                               (coe v7) (coe v10) in
                     coe
                       (let v14
                              = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
                                  (coe v8) (coe v11) in
                        coe
                          (case coe v13 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                               -> if coe v15
                                    then coe
                                           seq (coe v16)
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                -> if coe v17
                                                     then coe
                                                            seq (coe v18)
                                                            (let v19
                                                                   = coe
                                                                       MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                       (coe
                                                                          MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                                                                       (coe
                                                                          MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                                          (coe
                                                                             MAlonzo.Code.Once.SigOp.Info.d_name_178
                                                                             (coe v9)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.CanonicalName.d_parts_8
                                                                          (coe
                                                                             MAlonzo.Code.Once.SigOp.Info.d_name_178
                                                                             (coe v12))) in
                                                             coe
                                                               (case coe v19 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                    -> if coe v20
                                                                         then let v22
                                                                                    = seq
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                           (coe v20)
                                                                                           (coe
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                              erased)) in
                                                                              coe
                                                                                (case coe v22 of
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                     -> if coe v23
                                                                                          then let v25
                                                                                                     = seq
                                                                                                         (coe
                                                                                                            v24)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                            (coe
                                                                                                               v23)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                               erased)) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v25 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                      -> if coe
                                                                                                              v26
                                                                                                           then coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v27)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                     (coe
                                                                                                                        v26)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                        erased))
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v27)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                     (coe
                                                                                                                        v26)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          else (let v25
                                                                                                      = seq
                                                                                                          (coe
                                                                                                             v24)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                             (coe
                                                                                                                v23)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v25 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                       -> if coe
                                                                                                               v26
                                                                                                            then coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v27)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                      (coe
                                                                                                                         v26)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                         erased))
                                                                                                            else coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v27)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                      (coe
                                                                                                                         v26)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         else (let v22
                                                                                     = seq
                                                                                         (coe v21)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                            (coe
                                                                                               v20)
                                                                                            (coe
                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                               coe
                                                                                 (case coe v22 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                      -> if coe v23
                                                                                           then let v25
                                                                                                      = seq
                                                                                                          (coe
                                                                                                             v24)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                             (coe
                                                                                                                v23)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                erased)) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v25 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                       -> if coe
                                                                                                               v26
                                                                                                            then coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v27)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                      (coe
                                                                                                                         v26)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                         erased))
                                                                                                            else coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v27)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                      (coe
                                                                                                                         v26)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           else (let v25
                                                                                                       = seq
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                              (coe
                                                                                                                 v23)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                                                                 coe
                                                                                                   (case coe
                                                                                                           v25 of
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                        -> if coe
                                                                                                                v26
                                                                                                             then coe
                                                                                                                    seq
                                                                                                                    (coe
                                                                                                                       v27)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                       (coe
                                                                                                                          v26)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                                          erased))
                                                                                                             else coe
                                                                                                                    seq
                                                                                                                    (coe
                                                                                                                       v27)
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                                       (coe
                                                                                                                          v26)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                     else coe
                                                            seq (coe v18)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                               (coe v17)
                                                               (coe
                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    else coe
                                           seq (coe v16)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                              (coe v15)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_Call_136 v9
        -> coe
             seq (coe v6)
             (case coe v5 of
                MAlonzo.Code.Once.IR.C_Call_136 v12
                  -> coe
                       du_'8799'IRH'45'Call'45'aux_824
                       (coe
                          MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116 (coe v9)
                          (coe v12))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-aux
d_'8799'IRH'45'aux_490 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'aux_490 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_'8799'IRH'45'aux_490 v0 v1 v2 v3 v4 v5 v6
du_'8799'IRH'45'aux_490 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'aux_490 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe du_'8799'IRH'45'diag_454 v0 v1 v2 v3 v4 v5 erased erased)
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v7)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize._≟IR_
d__'8799'IR__536 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IR__536 v0 v1 v2 v3
  = coe
      du_'8799'IRH_436 (coe v0) (coe v1) (coe v0) (coe v1) (coe v2)
      (coe v3)
-- Once.Optimize.μ-inj
d_μ'45'inj_546 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_μ'45'inj_546 = erased
-- Once.Optimize.*-injˡ
d_'42''45'inj'737'_556 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'inj'737'_556 = erased
-- Once.Optimize.*-injʳ
d_'42''45'inj'691'_566 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'inj'691'_566 = erased
-- Once.Optimize.ν-inj
d_ν'45'inj_572 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ν'45'inj_572 = erased
-- Once.Optimize.≟IRH-∘-inner
d_'8799'IRH'45''8728''45'inner_588 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'inner_588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                   v8
  = du_'8799'IRH'45''8728''45'inner_588 v7 v8
du_'8799'IRH'45''8728''45'inner_588 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'inner_588 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-∘-aux
d_'8799'IRH'45''8728''45'aux_650 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''8728''45'aux_650 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8799'IRH'45''8728''45'aux_650 v0 v1 v3 v4 v5 v6 v7 v8
du_'8799'IRH'45''8728''45'aux_650 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''8728''45'aux_650 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       du_'8799'IRH'45''8728''45'inner_588
                       (coe
                          du_'8799'IRH_436 (coe v1) (coe v2) (coe v1) (coe v2) (coe v3)
                          (coe v5))
                       (coe
                          du_'8799'IRH_436 (coe v0) (coe v1) (coe v0) (coe v1) (coe v4)
                          (coe v6)))
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v8)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-⟨,⟩-aux
d_'8799'IRH'45''10216''44''10217''45'aux_686 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45''10216''44''10217''45'aux_686 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 v7 v8
  = du_'8799'IRH'45''10216''44''10217''45'aux_686 v7 v8
du_'8799'IRH'45''10216''44''10217''45'aux_686 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45''10216''44''10217''45'aux_686 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-case-aux
d_'8799'IRH'45'case'45'aux_746 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'case'45'aux_746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_'8799'IRH'45'case'45'aux_746 v7 v8
du_'8799'IRH'45'case'45'aux_746 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'case'45'aux_746 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.≟IRH-curry-aux
d_'8799'IRH'45'curry'45'aux_802 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'curry'45'aux_802 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8799'IRH'45'curry'45'aux_802 v5
du_'8799'IRH'45'curry'45'aux_802 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'curry'45'aux_802 v0
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
-- Once.Optimize.≟IRH-Call-aux
d_'8799'IRH'45'Call'45'aux_824 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRH'45'Call'45'aux_824 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8799'IRH'45'Call'45'aux_824 v4
du_'8799'IRH'45'Call'45'aux_824 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRH'45'Call'45'aux_824 v0
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
-- Once.Optimize._.≟const-irrelevant
d_'8799'const'45'irrelevant_1514
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Optimize._.\8799const-irrelevant"
-- Once.Optimize.dec-to-bool
d_dec'45'to'45'bool_1520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_dec'45'to'45'bool_1520 ~v0 ~v1 v2 = du_dec'45'to'45'bool_1520 v2
du_dec'45'to'45'bool_1520 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
du_dec'45'to'45'bool_1520 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe seq (coe v2) (coe v1)
             else coe seq (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-Void
d_is'45'Void_1522 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_is'45'Void_1522 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isUnitType
d_isUnitType_1524 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_isUnitType_1524 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.isVoidType
d_isVoidType_1526 :: MAlonzo.Code.Once.Type.T_Type_108 -> Bool
d_isVoidType_1526 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'42'__124 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'43'__126 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_rigid_138 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.is-fst?
d_is'45'fst'63'_1532 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'fst'63'_1532 ~v0 ~v1 v2 = du_is'45'fst'63'_1532 v2
du_is'45'fst'63'_1532 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'fst'63'_1532 v0
  = coe
      du_dec'45'to'45'bool_1520
      (coe
         d__'8799'IRHead__62 (coe du_ir'45'head_90 (coe v0))
         (coe C_h'45'fst_12))
-- Once.Optimize.is-snd?
d_is'45'snd'63'_1540 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'snd'63'_1540 ~v0 ~v1 v2 = du_is'45'snd'63'_1540 v2
du_is'45'snd'63'_1540 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'snd'63'_1540 v0
  = coe
      du_dec'45'to'45'bool_1520
      (coe
         d__'8799'IRHead__62 (coe du_ir'45'head_90 (coe v0))
         (coe C_h'45'snd_14))
-- Once.Optimize.is-terminal?
d_is'45'terminal'63'_1548 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_is'45'terminal'63'_1548 ~v0 ~v1 v2
  = du_is'45'terminal'63'_1548 v2
du_is'45'terminal'63'_1548 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_is'45'terminal'63'_1548 v0
  = coe
      du_dec'45'to'45'bool_1520
      (coe
         d__'8799'IRHead__62 (coe du_ir'45'head_90 (coe v0))
         (coe C_h'45'terminal_22))
-- Once.Optimize.safe-pair-distrib
d_safe'45'pair'45'distrib_1560 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_safe'45'pair'45'distrib_1560 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_safe'45'pair'45'distrib_1560 v4 v5
du_safe'45'pair'45'distrib_1560 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_safe'45'pair'45'distrib_1560 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe du_is'45'fst'63'_1532 (coe v0))
         (coe du_is'45'snd'63'_1540 (coe v1)))
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe du_is'45'snd'63'_1540 (coe v0))
            (coe du_is'45'fst'63'_1532 (coe v1)))
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
            (coe du_is'45'terminal'63'_1548 (coe v0))
            (coe du_is'45'terminal'63'_1548 (coe v1))))
-- Once.Optimize.wants-coprod
d_wants'45'coprod_1570 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_wants'45'coprod_1570 ~v0 ~v1 v2 = du_wants'45'coprod_1570 v2
du_wants'45'coprod_1570 :: MAlonzo.Code.Once.IR.T_IR_16 -> Bool
du_wants'45'coprod_1570 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe
         du_dec'45'to'45'bool_1520
         (coe
            d__'8799'IRHead__62 (coe du_ir'45'head_90 (coe v0))
            (coe C_h'45'case_20)))
      (coe
         du_dec'45'to'45'bool_1520
         (coe
            d__'8799'IRHead__62 (coe du_ir'45'head_90 (coe v0))
            (coe C_h'45'terminal_22)))
-- Once.Optimize.PairView
d_PairView_1580 a0 a1 a2 a3 = ()
data T_PairView_1580
  = C_is'45'pair_1592 | C_is'45'other'45'pair_1602
-- Once.Optimize.CoprodView
d_CoprodView_1610 a0 a1 a2 a3 = ()
data T_CoprodView_1610
  = C_is'45'inl_1616 | C_is'45'inr_1622 |
    C_is'45'other'45'coprod_1632
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_1638 a0 a1 a2 = ()
data T_ComposeFirstView_1638
  = C_cf'45'id_1642 | C_cf'45'terminal_1646 | C_cf'45'fst_1652 |
    C_cf'45'snd_1658 | C_cf'45'case_1670 | C_cf'45'other_1678
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_1684 a0 a1 a2 = ()
data T_ComposeSecondView_1684
  = C_cs'45'id_1688 | C_cs'45'initial_1692 | C_cs'45'other_1700
-- Once.Optimize.FstSndView
d_FstSndView_1706 a0 a1 a2 = ()
data T_FstSndView_1706
  = C_fsv'45'fst_1712 | C_fsv'45'snd_1718 | C_fsv'45'other_1726
-- Once.Optimize.InlInrView
d_InlInrView_1732 a0 a1 a2 = ()
data T_InlInrView_1732
  = C_iiv'45'inl_1738 | C_iiv'45'inr_1744 | C_iiv'45'other_1752
-- Once.Optimize.pairView-gen
d_pairView'45'gen_1766 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_1580
d_pairView'45'gen_1766 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_1766 v2
du_pairView'45'gen_1766 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_1580
du_pairView'45'gen_1766 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'pair_1592
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_curry_84 v4
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_const_124 v2 v3
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3
        -> coe C_is'45'other'45'pair_1602
      MAlonzo.Code.Once.IR.C_Call_136 v3
        -> coe C_is'45'other'45'pair_1602
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_1854 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_1580
d_pairView_1854 ~v0 ~v1 ~v2 v3 = du_pairView_1854 v3
du_pairView_1854 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_1580
du_pairView_1854 v0 = coe du_pairView'45'gen_1766 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_1870 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CoprodView_1610
d_coprodView'45'gen_1870 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_1870 v2
du_coprodView'45'gen_1870 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_1610
du_coprodView'45'gen_1870 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'inl_1616
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'inr_1622
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_curry_84 v4
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_Out_110 v2
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_const_124 v2 v3
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3
        -> coe C_is'45'other'45'coprod_1632
      MAlonzo.Code.Once.IR.C_Call_136 v3
        -> coe C_is'45'other'45'coprod_1632
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_1956 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_1610
d_coprodView_1956 ~v0 ~v1 ~v2 v3 = du_coprodView_1956 v3
du_coprodView_1956 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_1610
du_coprodView_1956 v0 = coe du_coprodView'45'gen_1870 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_1966 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_1638
d_composeFirstView_1966 ~v0 ~v1 v2 = du_composeFirstView_1966 v2
du_composeFirstView_1966 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_1638
du_composeFirstView_1966 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_1642
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_1652
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_1658
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_1670
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_1646
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_const_124 v2 v3 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3 -> coe C_cf'45'other_1678
      MAlonzo.Code.Once.IR.C_Call_136 v3 -> coe C_cf'45'other_1678
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_2012 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_1684
d_composeSecondView_2012 ~v0 ~v1 v2 = du_composeSecondView_2012 v2
du_composeSecondView_2012 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_1684
du_composeSecondView_2012 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_1688
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_1692
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_const_124 v2 v3 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3 -> coe C_cs'45'other_1700
      MAlonzo.Code.Once.IR.C_Call_136 v3 -> coe C_cs'45'other_1700
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_2058 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_1706
d_fstSndView_2058 ~v0 ~v1 v2 = du_fstSndView_2058 v2
du_fstSndView_2058 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_1706
du_fstSndView_2058 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_1712
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_1718
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_const_124 v2 v3 -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3
        -> coe C_fsv'45'other_1726
      MAlonzo.Code.Once.IR.C_Call_136 v3 -> coe C_fsv'45'other_1726
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_2104 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_1732
d_inlInrView_2104 ~v0 ~v1 v2 = du_inlInrView_2104 v2
du_inlInrView_2104 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_1732
du_inlInrView_2104 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_1738
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_1744
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_Ana_120 v2 v4 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_const_124 v2 v3 -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_SigOp_130 v1 v2 v3
        -> coe C_iiv'45'other_1752
      MAlonzo.Code.Once.IR.C_Call_136 v3 -> coe C_iiv'45'other_1752
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_2148 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_2148 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_2148 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_2148 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_2148 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_2148 (coe v0) (coe v9) (coe v7))
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
                    (coe d_has'45'effect'63'_2148 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_2148 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_2148
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
                           d_has'45'effect'63'_2148
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
      MAlonzo.Code.Once.IR.C_Ana_120 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    d_has'45'effect'63'_2148 (coe v0)
                    (coe
                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v7) (coe v0))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_SigOp_130 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_Call_136 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_2174 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_2174 ~v0 v1 v2 v3
  = du_optimize'45'fst_2174 v1 v2 v3
du_optimize'45'fst_2174 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'fst_2174 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_1766 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_1592
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v12
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_1602
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_fst_42) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-snd
d_optimize'45'snd_2196 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_2196 ~v0 v1 v2 v3
  = du_optimize'45'snd_2196 v1 v2 v3
du_optimize'45'snd_2196 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'snd_2196 v0 v1 v2
  = let v3 = coe du_pairView'45'gen_1766 (coe v2) in
    coe
      (case coe v3 of
         C_is'45'pair_1592
           -> case coe v2 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v12 v13 -> coe v13
                _ -> MAlonzo.RTE.mazUnreachableError
         C_is'45'other'45'pair_1602
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_snd_48) v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_2220 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_2220 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_2220 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_2220 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_2220 v0 v1 v2 v3 v4
  = let v5 = coe du_coprodView'45'gen_1870 (coe v4) in
    coe
      (case coe v5 of
         C_is'45'inl_1616 -> coe v2
         C_is'45'inr_1622 -> coe v3
         C_is'45'other'45'coprod_1632
           -> coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
                (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_2290 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_2290 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_2290 v1 v3 v4
du_optimize'45'compose'45'second_2290 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_2290 v0 v1 v2
  = let v3 = coe du_composeSecondView_2012 (coe v2) in
    coe
      (case coe v3 of
         C_cs'45'id_1688 -> coe v1
         C_cs'45'initial_1692 -> coe MAlonzo.Code.Once.IR.C_initial_76
         C_cs'45'other_1700
           -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-compose
d_optimize'45'compose_2320 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_2320 v0 v1 v2 v3 v4
  = let v5 = d_has'45'effect'63'_2148 (coe v0) (coe v1) (coe v4) in
    coe
      (if coe v5
         then coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v3 v4
         else (let v6 = coe du_composeFirstView_1966 (coe v3) in
               coe
                 (case coe v6 of
                    C_cf'45'id_1642 -> coe v4
                    C_cf'45'terminal_1646 -> coe MAlonzo.Code.Once.IR.C_terminal_72
                    C_cf'45'fst_1652
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'fst_2174 (coe v2) (coe v10) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'snd_1658
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
                             -> coe du_optimize'45'snd_2196 (coe v9) (coe v2) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'case_1670
                      -> case coe v1 of
                           MAlonzo.Code.Once.IRTy.C__'43'__22 v12 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Once.IR.C_case_68 v17 v18
                                    -> coe
                                         du_optimize'45'post'45'case_2220 (coe v12) (coe v13)
                                         (coe v17) (coe v18) (coe v4)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    C_cf'45'other_1678
                      -> coe
                           du_optimize'45'compose'45'second_2290 (coe v1) (coe v3) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Optimize.optimize-pair-aux
d_optimize'45'pair'45'aux_2382 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_1706 ->
  T_FstSndView_1706 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair'45'aux_2382 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'pair'45'aux_2382 v3 v4 v5 v6
du_optimize'45'pair'45'aux_2382 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FstSndView_1706 ->
  T_FstSndView_1706 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair'45'aux_2382 v0 v1 v2 v3
  = case coe v2 of
      C_fsv'45'fst_1712
        -> case coe v3 of
             C_fsv'45'fst_1712
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_1718 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_fsv'45'other_1726
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_fst_42) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'snd_1718
        -> case coe v3 of
             C_fsv'45'fst_1712
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_1718
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_1726
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe MAlonzo.Code.Once.IR.C_snd_48) v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fsv'45'other_1726
        -> case coe v3 of
             C_fsv'45'fst_1712
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             C_fsv'45'snd_1718
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0
                    (coe MAlonzo.Code.Once.IR.C_snd_48)
             C_fsv'45'other_1726
               -> coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_2426 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_2426 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'pair_2426 v3 v4
du_optimize'45'pair_2426 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'pair_2426 v0 v1
  = coe
      du_optimize'45'pair'45'aux_2382 (coe v0) (coe v1)
      (coe du_fstSndView_2058 (coe v0)) (coe du_fstSndView_2058 (coe v1))
-- Once.Optimize.optimize-case-aux
d_optimize'45'case'45'aux_2442 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_1732 ->
  T_InlInrView_1732 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case'45'aux_2442 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_optimize'45'case'45'aux_2442 v3 v4 v5 v6
du_optimize'45'case'45'aux_2442 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_InlInrView_1732 ->
  T_InlInrView_1732 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case'45'aux_2442 v0 v1 v2 v3
  = case coe v2 of
      C_iiv'45'inl_1738
        -> case coe v3 of
             C_iiv'45'inl_1738
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_1744 -> coe MAlonzo.Code.Once.IR.C_id_20
             C_iiv'45'other_1752
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inl_54)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'inr_1744
        -> case coe v3 of
             C_iiv'45'inl_1738
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_1744
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_1752
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 (coe MAlonzo.Code.Once.IR.C_inr_60)
                    v1
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iiv'45'other_1752
        -> case coe v3 of
             C_iiv'45'inl_1738
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
             C_iiv'45'inr_1744
               -> coe
                    MAlonzo.Code.Once.IR.C_case_68 v0
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
             C_iiv'45'other_1752 -> coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_2486 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_2486 ~v0 ~v1 ~v2 v3 v4
  = du_optimize'45'case_2486 v3 v4
du_optimize'45'case_2486 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'case_2486 v0 v1
  = coe
      du_optimize'45'case'45'aux_2442 (coe v0) (coe v1)
      (coe du_inlInrView_2104 (coe v0)) (coe du_inlInrView_2104 (coe v1))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_2496 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_2496 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_2320 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_2502 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_2502 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    du_optimize'45'pair_2426
                    (coe d_optimize'45'once_2502 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_2502 (coe v0) (coe v9) (coe v7))
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
                 = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
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
                    du_optimize'45'case_2486
                    (coe d_optimize'45'once_2502 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_2502 (coe v9) (coe v1) (coe v7))
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
                    (d_optimize'45'once_2502
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
                           (d_optimize'45'once_2502
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
      MAlonzo.Code.Once.IR.C_Ana_120 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    MAlonzo.Code.Once.IR.C_Ana_120 v4
                    (d_optimize'45'once_2502
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v7) (coe v0))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_124 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_130 v3 v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
                     (coe v3) (coe MAlonzo.Code.Once.Type.C_Void_122) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                       else coe seq (coe v8) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_Call_136 v5
        -> coe MAlonzo.Code.Once.IR.C_Call_136 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_2502 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_2502 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
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
                              = d_has'45'effect'63'_2148
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_2496 (coe v0)
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
                                              d_optimize'45'once'45'structural_2496 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_2650 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_2650 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_2650 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_2502 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_2662 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_2662 v0 v1
  = coe d_optimize'45'n_2650 (coe v0) (coe v1) (coe (10 :: Integer))
