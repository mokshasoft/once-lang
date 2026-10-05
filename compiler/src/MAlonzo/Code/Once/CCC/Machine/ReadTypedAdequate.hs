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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ReadTypedAdequate._.readReg-typed
d_readReg'45'typed_108 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readReg'45'typed_108 ~v0 ~v1 ~v2 = du_readReg'45'typed_108
du_readReg'45'typed_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readReg'45'typed_108
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readReg'45'typed_2774
-- Once.CCC.Machine.ReadTypedAdequate._.readTyped
d_readTyped_110 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Maybe AgdaAny
d_readTyped_110 ~v0 ~v1 ~v2 = du_readTyped_110
du_readTyped_110 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  Maybe AgdaAny
du_readTyped_110
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2830
-- Once.CCC.Machine.ReadTypedAdequate._.readTyped-cell
d_readTyped'45'cell_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
d_readTyped'45'cell_112 ~v0 ~v1 ~v2 = du_readTyped'45'cell_112
du_readTyped'45'cell_112 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
   Maybe AgdaAny) ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   Maybe AgdaAny) ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe AgdaAny
du_readTyped'45'cell_112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped'45'cell_2722 v1
      v2 v3
-- Once.CCC.Machine.ReadTypedAdequate._.readLoc
d_readLoc_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_142 ~v0 ~v1 ~v2 = du_readLoc_142
du_readLoc_142 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_142
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_666
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.CellAt
d_CellAt_184 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.InlineRep
d_InlineRep_218 a0 a1 a2 a3 a4 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.SumTag
d_SumTag_238 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_238 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_240 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.ClosureWellFormedDef.inline-sv
d_inline'45'sv_320 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_568 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_320 ~v0 ~v1 ~v2 = du_inline'45'sv_320
du_inline'45'sv_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_568 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_320 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_578
      v2 v3
-- Once.CCC.Machine.ReadTypedAdequate._.CellAt
d_CellAt_778 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.InlineRep
d_InlineRep_780 a0 a1 a2 a3 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.SumTag
d_SumTag_782 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 -> ()
d_SumTag_782 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.ValidAtWF
d_ValidAtWF_784 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.CCC.Machine.ReadTypedAdequate._.inline-sv
d_inline'45'sv_790 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_568 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_inline'45'sv_790 ~v0 ~v1 ~v2 = du_inline'45'sv_790
du_inline'45'sv_790 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_568 ->
  AgdaAny -> MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_inline'45'sv_790 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_inline'45'sv_578
      v1 v2
-- Once.CCC.Machine.ReadTypedAdequate.Readable
d_Readable_852 a0 a1 a2 a3 = ()
data T_Readable_852
  = C_r'45'unit_854 | C_r'45'int_856 |
    C_r'45'pair_862 T_Readable_852 T_Readable_852 | C_r'45'float_864 |
    C_r'45'sum_870 T_Readable_852 T_Readable_852 | C_r'45'void_872 |
    C_r'45'rigid_878
-- Once.CCC.Machine.ReadTypedAdequate.readable-base
d_readable'45'base_882 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  T_Readable_852
d_readable'45'base_882 ~v0 ~v1 ~v2 v3 v4
  = du_readable'45'base_882 v3 v4
du_readable'45'base_882 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  T_Readable_852
du_readable'45'base_882 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
        -> coe C_r'45'unit_854
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_200
        -> coe C_r'45'void_872
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202
        -> coe C_r'45'int_856
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204
        -> coe C_r'45'float_864
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v6 v7
               -> coe
                    C_r'45'pair_862 (coe du_readable'45'base_882 (coe v6) (coe v4))
                    (coe du_readable'45'base_882 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v6 v7
               -> coe
                    C_r'45'sum_870 (coe du_readable'45'base_882 (coe v6) (coe v4))
                    (coe du_readable'45'base_882 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'rigid_220
        -> coe C_r'45'rigid_878
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ReadTypedAdequate.readable?
d_readable'63'_894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe T_Readable_852
d_readable'63'_894 ~v0 ~v1 ~v2 v3 = du_readable'63'_894 v3
du_readable'63'_894 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> Maybe T_Readable_852
du_readable'63'_894 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_120
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'unit_854)
         MAlonzo.Code.Once.Type.C_Void_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'void_872)
         MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
           -> let v4 = coe du_readable'63'_894 (coe v2) in
              coe
                (let v5 = coe du_readable'63'_894 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_r'45'pair_862 v6 v7)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
           -> let v4 = coe du_readable'63'_894 (coe v2) in
              coe
                (let v5 = coe du_readable'63'_894 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_r'45'sum_870 v6 v7)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.Type.C_Int_134
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'int_856)
         MAlonzo.Code.Once.Type.C_Float_136
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'float_864)
         MAlonzo.Code.Once.Type.C_rigid_138 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'rigid_878)
         _ -> coe v1)
-- Once.CCC.Machine.ReadTypedAdequate.subst-×-cong₂
d_subst'45''215''45'cong'8322'_952 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
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
d_subst'45''215''45'cong'8322'_952 = erased
-- Once.CCC.Machine.ReadTypedAdequate.subst-⊎₁
d_subst'45''8846''8321'_972 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8846''8321'_972 = erased
-- Once.CCC.Machine.ReadTypedAdequate.subst-⊎₂
d_subst'45''8846''8322'_990 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8846''8322'_990 = erased
-- Once.CCC.Machine.ReadTypedAdequate.sumtag-eq
d_sumtag'45'eq_1002 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sumtag'45'eq_1002 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-cell-adequate
d_readTyped'45'cell'45'adequate_1024 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_Readable_852 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_590 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'cell'45'adequate_1024 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-adequate
d_readTyped'45'adequate_1042 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_Readable_852 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_594 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_1042 = erased
-- Once.CCC.Machine.ReadTypedAdequate._.unit-cell
d_unit'45'cell_1236 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_InlineRep_568 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unit'45'cell_1236 = erased
