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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.CCC.Machine.ReadTypedAdequate._.readReg-typed
d_readReg'45'typed_108 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_108 ~v0 ~v1 ~v2 = du_readReg'45'typed_108
du_readReg'45'typed_108 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_108
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2744
-- Once.CCC.Machine.ReadTypedAdequate._.readTyped
d_readTyped_110 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe AgdaAny
d_readTyped_110 ~v0 ~v1 ~v2 = du_readTyped_110
du_readTyped_110 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  Maybe AgdaAny
du_readTyped_110
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2800
-- Once.CCC.Machine.ReadTypedAdequate._.readTyped-cell
d_readTyped'45'cell_112 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readTyped'45'cell_112 ~v0 ~v1 ~v2 = du_readTyped'45'cell_112
du_readTyped'45'cell_112 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readTyped'45'cell_112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'cell_2692 v1
      v2 v3
-- Once.CCC.Machine.ReadTypedAdequate._.readLoc
d_readLoc_142 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_142 ~v0 ~v1 ~v2 = du_readLoc_142
du_readLoc_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_142
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.CellAt
d_CellAt_180 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.InlineRep
d_InlineRep_194 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.SumTag
d_SumTag_212 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_212 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_214 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_250 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_250 ~v0 ~v1 ~v2 = du_inline'45'sv_250
du_inline'45'sv_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_250 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
      v2 v3
-- Once.CCC.Machine.ReadTypedAdequate._.CellAt
d_CellAt_462 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.InlineRep
d_InlineRep_464 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.SumTag
d_SumTag_466 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_466 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.ValidAtWF
d_ValidAtWF_468 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.inline-sv
d_inline'45'sv_474 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_474 ~v0 ~v1 ~v2 = du_inline'45'sv_474
du_inline'45'sv_474 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_474 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_566
      v1 v2
-- Once.CCC.Machine.ReadTypedAdequate.Readable
d_Readable_534 a0 a1 a2 a3 = ()
data T_Readable_534
  = C_r'45'unit_536 | C_r'45'int_538 |
    C_r'45'pair_544 T_Readable_534 T_Readable_534 | C_r'45'float_546 |
    C_r'45'sum_552 T_Readable_534 T_Readable_534 | C_r'45'void_554 |
    C_r'45'rigid_560
-- Once.CCC.Machine.ReadTypedAdequate.readable-base
d_readable'45'base_564 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  T_Readable_534
d_readable'45'base_564 ~v0 ~v1 ~v2 v3 v4
  = du_readable'45'base_564 v3 v4
du_readable'45'base_564 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  T_Readable_534
du_readable'45'base_564 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10
        -> coe C_r'45'unit_536
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Void_12
        -> coe C_r'45'void_554
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14
        -> coe C_r'45'int_538
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16
        -> coe C_r'45'float_546
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Prod_22 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v6 v7
               -> coe
                    C_r'45'pair_544 (coe du_readable'45'base_564 (coe v6) (coe v4))
                    (coe du_readable'45'base_564 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Sum_28 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v6 v7
               -> coe
                    C_r'45'sum_552 (coe du_readable'45'base_564 (coe v6) (coe v4))
                    (coe du_readable'45'base_564 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'rigid_32
        -> coe C_r'45'rigid_560
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ReadTypedAdequate.readable?
d_readable'63'_576 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe T_Readable_534
d_readable'63'_576 ~v0 ~v1 ~v2 v3 = du_readable'63'_576 v3
du_readable'63'_576 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> Maybe T_Readable_534
du_readable'63'_576 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Type.C_Unit_20
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'unit_536)
         MAlonzo.Code.Once.Lang.Type.C_Void_22
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'void_554)
         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3
           -> let v4 = coe du_readable'63'_576 (coe v2) in
              coe
                (let v5 = coe du_readable'63'_576 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_r'45'pair_544 v6 v7)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3
           -> let v4 = coe du_readable'63'_576 (coe v2) in
              coe
                (let v5 = coe du_readable'63'_576 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_r'45'sum_552 v6 v7)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.Lang.Type.C_Int_34
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'int_538)
         MAlonzo.Code.Once.Lang.Type.C_Float_36
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'float_546)
         MAlonzo.Code.Once.Lang.Type.C_rigid_38 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'rigid_560)
         _ -> coe v1)
-- Once.CCC.Machine.ReadTypedAdequate.subst-×-cong₂
d_subst'45''215''45'cong'8322'_634 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''215''45'cong'8322'_634 = erased
-- Once.CCC.Machine.ReadTypedAdequate.subst-⊎₁
d_subst'45''8846''8321'_654 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8846''8321'_654 = erased
-- Once.CCC.Machine.ReadTypedAdequate.subst-⊎₂
d_subst'45''8846''8322'_672 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8846''8322'_672 = erased
-- Once.CCC.Machine.ReadTypedAdequate.sumtag-eq
d_sumtag'45'eq_684 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumtag'45'eq_684 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-cell-adequate
d_readTyped'45'cell'45'adequate_706 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Readable_534 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_578 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'cell'45'adequate_706 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-adequate
d_readTyped'45'adequate_724 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  T_Readable_534 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_582 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_724 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.unit-cell
d_unit'45'cell_918 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_408 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_556 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unit'45'cell_918 = erased
