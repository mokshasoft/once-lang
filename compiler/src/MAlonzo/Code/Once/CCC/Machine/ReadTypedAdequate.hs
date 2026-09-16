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

module MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ReadTypedAdequate._.readReg-typed
d_readReg'45'typed_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_90 ~v0 ~v1 = du_readReg'45'typed_90
du_readReg'45'typed_90 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_90
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2728
-- Once.CCC.Machine.ReadTypedAdequate._.readTyped
d_readTyped_92 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
d_readTyped_92 ~v0 ~v1 = du_readTyped_92
du_readTyped_92 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Maybe AgdaAny
du_readTyped_92
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2734
-- Once.CCC.Machine.ReadTypedAdequate._.readTyped-cell
d_readTyped'45'cell_94 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readTyped'45'cell_94 ~v0 ~v1 = du_readTyped'45'cell_94
du_readTyped'45'cell_94 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readTyped'45'cell_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'cell_2676 v1
      v2 v3
-- Once.CCC.Machine.ReadTypedAdequate._.readLoc
d_readLoc_114 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_114 ~v0 ~v1 = du_readLoc_114
du_readLoc_114 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_114
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.CellAt
d_CellAt_156 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.InlineRep
d_InlineRep_192 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_218 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_300 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_300 ~v0 ~v1 = du_inline'45'sv_300
du_inline'45'sv_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_300 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_572
      v2 v3
-- Once.CCC.Machine.ReadTypedAdequate._.CellAt
d_CellAt_788 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.InlineRep
d_InlineRep_790 a0 a1 a2 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ValidAtWF
d_ValidAtWF_792 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.inline-sv
d_inline'45'sv_798 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_798 ~v0 ~v1 = du_inline'45'sv_798
du_inline'45'sv_798 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_798 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_572
      v1 v2
-- Once.CCC.Machine.ReadTypedAdequate.Readable
d_Readable_854 a0 a1 a2 = ()
data T_Readable_854
  = C_r'45'unit_856 | C_r'45'int_858 |
    C_r'45'pair_864 T_Readable_854 T_Readable_854
-- Once.CCC.Machine.ReadTypedAdequate.readable?
d_readable'63'_868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe T_Readable_854
d_readable'63'_868 ~v0 ~v1 v2 = du_readable'63'_868 v2
du_readable'63'_868 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe T_Readable_854
du_readable'63'_868 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_118
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'unit_856)
         MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
           -> let v4 = coe du_readable'63'_868 (coe v2) in
              coe
                (let v5 = coe du_readable'63'_868 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_r'45'pair_864 v6 v7)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.Type.C_Int_132
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'int_858)
         _ -> coe v1)
-- Once.CCC.Machine.ReadTypedAdequate.subst-×-cong₂
d_subst'45''215''45'cong'8322'_906 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''215''45'cong'8322'_906 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-cell-adequate
d_readTyped'45'cell'45'adequate_926 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_Readable_854 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'cell'45'adequate_926 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-adequate
d_readTyped'45'adequate_942 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_Readable_854 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_942 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.unit-cell
d_unit'45'cell_998 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_562 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unit'45'cell_998 = erased
