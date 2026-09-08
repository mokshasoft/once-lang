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
-- Once.CCC.Machine.ShapeAt.ShapeAt
d_ShapeAt_94 a0 a1 a2 a3 a4 a5 = ()
data T_ShapeAt_94
  = C_shape'45'unit_104 |
    C_shape'45'pair_126 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                        MAlonzo.Code.Once.IR.T_AllocMode_4
                        MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                        T_ShapeAt_94 T_ShapeAt_94 |
    C_shape'45'closure_148 MAlonzo.Code.Once.IRTy.T_IRTy_6
                           MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                           MAlonzo.Code.Once.IR.T_AllocMode_4
                           MAlonzo.Code.Once.CCC.Label.T_LabelId_6 AgdaAny
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                           T_ShapeAt_94 |
    C_shape'45'inl_166 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ShapeAt_94 |
    C_shape'45'inr_184 MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12
                       MAlonzo.Code.Once.IR.T_AllocMode_4 AgdaAny
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
                       T_ShapeAt_94 |
    C_shape'45'inl'45'reg_202 AgdaAny AgdaAny T_InlineRepAt_76
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'inr'45'reg_220 AgdaAny AgdaAny T_InlineRepAt_76
                              MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'μ_234 MAlonzo.Code.Once.IRTy.T_WellFormedFI_130
                     T_ShapeAt_94 |
    C_shape'45'ν_248 MAlonzo.Code.Once.IRTy.T_WellFormedFI_130
                     T_ShapeAt_94 |
    C_shape'45'int_260 Integer
                       MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'float_272 Integer
                         MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'str_282 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658 |
    C_shape'45'buffer_292 MAlonzo.Code.Once.CCC.Machine.Allocation.T_BeforeFrontier_658
-- Once.CCC.Machine.ShapeAt.Project._.SumTag
d_SumTag_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_302 = erased
-- Once.CCC.Machine.ShapeAt.Project._.ValidAtWF
d_ValidAtWF_304 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ShapeAt.Project.tag-of
d_tag'45'of_372 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> AgdaAny
d_tag'45'of_372 = erased
-- Once.CCC.Machine.ShapeAt.Project.valid→shape
d_valid'8594'shape_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_570 ->
  T_ShapeAt_94
d_valid'8594'shape_402 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9
  = du_valid'8594'shape_402 v0 v5 v6 v9
du_valid'8594'shape_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_570 ->
  T_ShapeAt_94
du_valid'8594'shape_402 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_760
        -> coe C_shape'45'unit_104
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_786 v11 v12 v14 v15 v16 v19 v20 v21 v22 v23
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v24 v25
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                      -> coe
                           C_shape'45'pair_126 v11 v12 v14 v15 v16 v19 v20 v21
                           (coe
                              du_valid'8594'shape_402 (coe v0) (coe v24) (coe v26) (coe v22))
                           (coe
                              du_valid'8594'shape_402 (coe v0) (coe v25) (coe v27) (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_816 v5 v8 v9 v11 v13 v15 v16 v17 v20 v21 v22 v23
        -> coe
             C_shape'45'closure_148 v5 v13 v15 v16 v17 v20 v21
             (coe du_valid'8594'shape_402 (coe v0) (coe v5) (coe v9) (coe v22))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_836 v10 v12 v13 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> coe
                           C_shape'45'inl_166 v10 v12 v13 v16 v17
                           (coe
                              du_valid'8594'shape_402 (coe v0) (coe v19) (coe v21) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_856 v10 v12 v13 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe
                           C_shape'45'inr_184 v10 v12 v13 v16 v17
                           (coe
                              du_valid'8594'shape_402 (coe v0) (coe v20) (coe v21) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'reg'45'wf_874 v11 v13 v15
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_554 v17
                      -> coe
                           seq (coe v17)
                           (coe
                              C_shape'45'inl'45'reg_202 v16 v11
                              (coe C_rep'45'prim'45'at_80 (coe v17)) v15)
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_556 v18
                      -> coe
                           C_shape'45'inl'45'reg_202 v16 v11 (coe C_rep'45'unit'45'at_82 v18)
                           v15
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'reg'45'wf_892 v11 v13 v15
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'prim_554 v17
                      -> coe
                           seq (coe v17)
                           (coe
                              C_shape'45'inr'45'reg_220 v16 v11
                              (coe C_rep'45'prim'45'at_80 (coe v17)) v15)
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_rep'45'unit_556 v18
                      -> coe
                           C_shape'45'inr'45'reg_220 v16 v11 (coe C_rep'45'unit'45'at_82 v18)
                           v15
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_908 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
               -> coe
                    C_shape'45'μ_234 v9
                    (coe
                       du_valid'8594'shape_402 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v1))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v9) v2)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'wf_924 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
               -> coe
                    C_shape'45'ν_248 v9
                    (coe
                       du_valid'8594'shape_402 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v1))
                       (coe
                          MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval_24 v0 v1
                          (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v12) (coe v1))
                          (coe MAlonzo.Code.Once.IR.C_Out_118 v9) v2)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_936 v9
        -> coe C_shape'45'int_260 v2 v9
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_948 v9
        -> coe C_shape'45'float_272 v2 v9
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_960 v9
        -> coe C_shape'45'str_282 v9
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_972 v9
        -> coe C_shape'45'buffer_292 v9
      _ -> MAlonzo.RTE.mazUnreachableError
