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

module MAlonzo.Code.Once.CCC.Machine.ShapeAt where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Eval
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.CCC.Machine.ShapeAt._.readLoc
d_readLoc_12 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
d_readLoc_12 ~v0 = du_readLoc_12
du_readLoc_12 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_68
du_readLoc_12
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_712
-- Once.CCC.Machine.ShapeAt._.BeforeFrontier
d_BeforeFrontier_16 a0 a1 a2 = ()
-- Once.CCC.Machine.ShapeAt.TagAt
d_TagAt_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_TagAt_26 = erased
-- Once.CCC.Machine.ShapeAt.tag-at-read
d_tag'45'at'45'read_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tag'45'at'45'read_48 = erased
-- Once.CCC.Machine.ShapeAt.ShapeAt
d_ShapeAt_66 a0 a1 a2 a3 a4 a5 = ()
data T_ShapeAt_66
  = C_shape'45'unit_76 |
    C_shape'45'pair_98 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ShapeAt_66 T_ShapeAt_66 |
    C_shape'45'closure_120 MAlonzo.Code.Once.IRTy.T_IRTy_6
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.IR.T_AllocMode_4 Integer AgdaAny
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                           T_ShapeAt_66 |
    C_shape'45'inl_138 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ShapeAt_66 |
    C_shape'45'inr_156 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
                       T_ShapeAt_66 |
    C_shape'45'μ_170 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                     T_ShapeAt_66 |
    C_shape'45'ν_184 MAlonzo.Code.Once.IRTy.T_WellFormedFI_114
                     T_ShapeAt_66 |
    C_shape'45'int_196 Integer
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_shape'45'float_208 MAlonzo.Code.Agda.Builtin.Float.T_Float_6
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_shape'45'str_218 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634 |
    C_shape'45'buffer_228 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_634
-- Once.CCC.Machine.ShapeAt.Project._.SumTag
d_SumTag_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_236 = erased
-- Once.CCC.Machine.ShapeAt.Project._.ValidAtWF
d_ValidAtWF_238 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ShapeAt.Project.tag-of
d_tag'45'of_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_tag'45'of_294 = erased
-- Once.CCC.Machine.ShapeAt.Project.valid→shape
d_valid'8594'shape_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
  T_ShapeAt_66
d_valid'8594'shape_324 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_valid'8594'shape_324 v4 v5 v8
du_valid'8594'shape_324 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
  T_ShapeAt_66
du_valid'8594'shape_324 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_766
        -> coe C_shape'45'unit_76
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_792 v10 v11 v13 v14 v15 v18 v19 v20 v21 v22
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v23 v24
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                      -> coe
                           C_shape'45'pair_98 v10 v11 v13 v14 v15 v18 v19 v20
                           (coe du_valid'8594'shape_324 (coe v23) (coe v25) (coe v21))
                           (coe du_valid'8594'shape_324 (coe v24) (coe v26) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_822 v4 v7 v8 v10 v12 v14 v15 v16 v19 v20 v21 v22
        -> coe
             C_shape'45'closure_120 v4 v12 v14 v15 v16 v19 v20
             (coe du_valid'8594'shape_324 (coe v4) (coe v8) (coe v21))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_842 v9 v11 v12 v15 v16 v17
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v18 v19
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> coe
                           C_shape'45'inl_138 v9 v11 v12 v15 v16
                           (coe du_valid'8594'shape_324 (coe v18) (coe v20) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_862 v9 v11 v12 v15 v16 v17
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v18 v19
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           C_shape'45'inr_156 v9 v11 v12 v15 v16
                           (coe du_valid'8594'shape_324 (coe v19) (coe v20) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_878 v8 v10
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v11
               -> coe
                    C_shape'45'μ_170 v8
                    (coe
                       du_valid'8594'shape_324
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v0))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v0))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v8) (coe v1))
                       (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'wf_894 v8 v10
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
               -> coe
                    C_shape'45'ν_184 v8
                    (coe
                       du_valid'8594'shape_324
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v0))
                       (coe
                          MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0)
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v11) (coe v0))
                          (coe MAlonzo.Code.Once.IR.C_Out_116 v8) (coe v1))
                       (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_906 v8
        -> coe C_shape'45'int_196 v1 v8
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_918 v8
        -> coe C_shape'45'float_208 v1 v8
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_930 v8
        -> coe C_shape'45'str_218 v8
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_942 v8
        -> coe C_shape'45'buffer_228 v8
      _ -> MAlonzo.RTE.mazUnreachableError
