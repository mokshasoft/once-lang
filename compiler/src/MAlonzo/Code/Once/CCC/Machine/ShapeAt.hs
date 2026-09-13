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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ShapeAt._.readLoc
d_readLoc_12 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_12 ~v0 = du_readLoc_12
du_readLoc_12 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_12
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.ShapeAt._.BeforeFrontier
d_BeforeFrontier_16 a0 a1 a2 = ()
-- Once.CCC.Machine.ShapeAt.TagAt
d_TagAt_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_TagAt_26 = erased
-- Once.CCC.Machine.ShapeAt.tag-at-read
d_tag'45'at'45'read_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tag'45'at'45'read_48 = erased
-- Once.CCC.Machine.ShapeAt.prim-sv-at
d_prim'45'sv'45'at_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_prim'45'sv'45'at_68 ~v0 ~v1 v2 v3 = du_prim'45'sv'45'at_68 v2 v3
du_prim'45'sv'45'at_68 ::
  MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_prim'45'sv'45'at_68 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IRTy.C_fits'45'int_528
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Int_132)
             (coe MAlonzo.Code.Once.Type.C_fits'45'int_194) (coe v1)
      MAlonzo.Code.Once.IRTy.C_fits'45'float_530
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_SV'45'Lit_76
             (coe MAlonzo.Code.Once.Type.C_Float_134)
             (coe MAlonzo.Code.Once.Type.C_fits'45'float_196) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ShapeAt.InlineRepAt
d_InlineRepAt_76 a0 a1 = ()
data T_InlineRepAt_76
  = C_rep'45'prim'45'at_80 MAlonzo.Code.Once.IRTy.T_FitsInRegI_526 |
    C_rep'45'unit'45'at_82 MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
-- Once.CCC.Machine.ShapeAt.inline-sv-at
d_inline'45'sv'45'at_86 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  T_InlineRepAt_76 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv'45'at_86 ~v0 ~v1 v2 v3
  = du_inline'45'sv'45'at_86 v2 v3
du_inline'45'sv'45'at_86 ::
  T_InlineRepAt_76 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv'45'at_86 v0 v1
  = case coe v0 of
      C_rep'45'prim'45'at_80 v2
        -> coe du_prim'45'sv'45'at_68 (coe v2) (coe v1)
      C_rep'45'unit'45'at_82 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ShapeAt.CellShapeAt
d_CellShapeAt_96 a0 a1 a2 a3 a4 = ()
data T_CellShapeAt_96
  = C_cell'45'shape'45'ptr_112 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                               MAlonzo.Code.Once.IR.T_AllocMode_4
                               MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                               T_ShapeAt_98 |
    C_cell'45'shape'45'inline_124 AgdaAny T_InlineRepAt_76
-- Once.CCC.Machine.ShapeAt.ShapeAt
d_ShapeAt_98 a0 a1 a2 a3 a4 a5 = ()
data T_ShapeAt_98
  = C_shape'45'unit_134 |
    C_shape'45'pair_148 AgdaAny
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        T_CellShapeAt_96 T_CellShapeAt_96 |
    C_shape'45'closure_170 MAlonzo.Code.Once.IRTy.T_IRTy_6
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.IR.T_AllocMode_4
                           MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           T_ShapeAt_98 |
    C_shape'45'inl_188 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ShapeAt_98 |
    C_shape'45'inr_206 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ShapeAt_98 |
    C_shape'45'closure'45'reg_228 MAlonzo.Code.Once.IRTy.T_IRTy_6
                                  AgdaAny MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                                  T_InlineRepAt_76
                                  MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'inl'45'reg_246 AgdaAny AgdaAny T_InlineRepAt_76
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'inr'45'reg_264 AgdaAny AgdaAny T_InlineRepAt_76
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'μ_278 MAlonzo.Code.Once.IRTy.T_WellFormedFI_130
                     T_ShapeAt_98 |
    C_shape'45'ν'45'susp_294 MAlonzo.Code.Once.IRTy.T_IRTy_6
                             MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny T_CellShapeAt_96
                             MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'int_306 Integer
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'float_318 Integer
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'str_328 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'buffer_338 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
-- Once.CCC.Machine.ShapeAt.Project._.CellAt
d_CellAt_348 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ShapeAt.Project._.SumTag
d_SumTag_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_350 = erased
-- Once.CCC.Machine.ShapeAt.Project._.ValidAtWF
d_ValidAtWF_352 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ShapeAt.Project.tag-of
d_tag'45'of_434 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_tag'45'of_434 = erased
-- Once.CCC.Machine.ShapeAt.Project.cell→shape
d_cell'8594'shape_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  T_CellShapeAt_96
d_cell'8594'shape_462 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_cell'8594'shape_462 v0 v1 v2 v3 v4 v5 v7 v8
du_cell'8594'shape_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_586 ->
  T_CellShapeAt_96
du_cell'8594'shape_462 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_788 v11 v13 v15 v16
        -> coe
             C_cell'45'shape'45'ptr_112 v11 v13 v15
             (coe
                du_valid'8594'shape_476 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11) (coe v6) (coe v16))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_800 v12
        -> case coe v12 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_568 v14
               -> coe
                    seq (coe v14)
                    (coe
                       C_cell'45'shape'45'inline_124 v5
                       (coe C_rep'45'prim'45'at_80 (coe v14)))
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_570 v15
               -> coe
                    C_cell'45'shape'45'inline_124 v5 (coe C_rep'45'unit'45'at_82 v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ShapeAt.Project.valid→shape
d_valid'8594'shape_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  T_ShapeAt_98
d_valid'8594'shape_476 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_valid'8594'shape_476 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_valid'8594'shape_476 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_590 ->
  T_ShapeAt_98
du_valid'8594'shape_476 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_810
        -> coe C_shape'45'unit_134
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_828 v17 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                      -> coe
                           C_shape'45'pair_148 v17 v18
                           (coe
                              du_cell'8594'shape_462 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v21) (coe v23) (coe v7) (coe v19))
                           (coe
                              du_cell'8594'shape_462 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v22) (coe v24) (coe v7) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_854 v9 v12 v13 v16 v18 v19 v20 v23 v24 v25
        -> coe
             C_shape'45'closure_170 v9 v16 v18 v19 v20 v23 v24
             (coe
                du_valid'8594'shape_476 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v9) (coe v13) (coe v16) (coe v7) (coe v25))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'reg'45'wf_878 v9 v12 v13 v17 v18 v19 v22
        -> case coe v19 of
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_568 v23
               -> case coe v23 of
                    MAlonzo.Code.Once.IRTy.C_fits'45'int_528
                      -> coe
                           C_shape'45'closure'45'reg_228 (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                           v13 v17 v18 (coe C_rep'45'prim'45'at_80 (coe v23)) v22
                    MAlonzo.Code.Once.IRTy.C_fits'45'float_530
                      -> coe
                           C_shape'45'closure'45'reg_228
                           (coe MAlonzo.Code.Once.IRTy.C_Float_32) v13 v17 v18
                           (coe C_rep'45'prim'45'at_80 (coe v23)) v22
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_570 v24
               -> coe
                    C_shape'45'closure'45'reg_228 v9 v13 v17 v18
                    (coe C_rep'45'unit'45'at_82 v24) v22
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_898 v10 v11 v12 v13 v17 v18 v19 v21
        -> coe
             C_shape'45'ν'45'susp_294 v10 v17 v18
             (coe
                du_cell'8594'shape_462 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v10) (coe v13) (coe v7) (coe v19))
             v21
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_918 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v26
                      -> coe
                           C_shape'45'inl_188 v15 v17 v18 v21 v22
                           (coe
                              du_valid'8594'shape_476 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v24) (coe v26) (coe v15) (coe v7) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_938 v15 v17 v18 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v24 v25
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v26
                      -> coe
                           C_shape'45'inr_206 v15 v17 v18 v21 v22
                           (coe
                              du_valid'8594'shape_476 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v25) (coe v26) (coe v15) (coe v7) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'reg'45'wf_956 v16 v18 v20
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
               -> case coe v18 of
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_568 v22
                      -> coe
                           seq (coe v22)
                           (coe
                              C_shape'45'inl'45'reg_246 v21 v16
                              (coe C_rep'45'prim'45'at_80 (coe v22)) v20)
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_570 v23
                      -> coe
                           C_shape'45'inl'45'reg_246 v21 v16 (coe C_rep'45'unit'45'at_82 v23)
                           v20
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'reg'45'wf_974 v16 v18 v20
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
               -> case coe v18 of
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_568 v22
                      -> coe
                           seq (coe v22)
                           (coe
                              C_shape'45'inr'45'reg_264 v21 v16
                              (coe C_rep'45'prim'45'at_80 (coe v22)) v20)
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_570 v23
                      -> coe
                           C_shape'45'inr'45'reg_264 v21 v16 (coe C_rep'45'unit'45'at_82 v23)
                           v20
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_990 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v17
               -> coe
                    C_shape'45'μ_278 v14
                    (coe
                       du_valid'8594'shape_476 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v17) (coe v4))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_30 v0
                             v4
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v17) (coe v4))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v14) v5)
                          (coe (0 :: Integer)))
                       (coe v6) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_1002 v14
        -> coe C_shape'45'int_306 v5 v14
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_1014 v14
        -> coe C_shape'45'float_318 v5 v14
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_1026 v14
        -> coe C_shape'45'str_328 v14
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_1038 v14
        -> coe C_shape'45'buffer_338 v14
      _ -> MAlonzo.RTE.mazUnreachableError
