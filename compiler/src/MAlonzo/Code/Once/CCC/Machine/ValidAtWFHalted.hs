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

module MAlonzo.Code.Once.CCC.Machine.ValidAtWFHalted where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
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
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.CCC.Machine.ValidAtWFHalted._.ClosureWellFormedDef.CellAt
d_CellAt_20 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Machine.ValidAtWFHalted._.ClosureWellFormedDef.ValidAtWF
d_ValidAtWF_82 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.CellAt
d_CellAt_664 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.ValidAtWF
d_ValidAtWF_726 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ValidAtWFHalted._._.readLoc
d_readLoc_1296 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
d_readLoc_1296 ~v0 ~v1 = du_readLoc_1296
du_readLoc_1296 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66
du_readLoc_1296
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readLoc_644
-- Once.CCC.Machine.ValidAtWFHalted._.rl
d_rl_1308 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rl_1308 = erased
-- Once.CCC.Machine.ValidAtWFHalted._.validAtWF-set-halted
d_validAtWF'45'set'45'halted_1330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
d_validAtWF'45'set'45'halted_1330 v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9
  = du_validAtWF'45'set'45'halted_1330 v0 v1 v3 v4 v5 v7 v8 v9
du_validAtWF'45'set'45'halted_1330 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_588
du_validAtWF'45'set'45'halted_1330 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_808
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'unit'45'wf_808
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_826 v16 v17 v18 v19
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v20 v21
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'pair'45'wf_826
                           v16 v17
                           (coe
                              du_cellAt'45'set'45'halted_1344 (coe v0) (coe v1) (coe v2)
                              (coe v20) (coe v22) (coe v5) (coe v6) (coe v18))
                           (coe
                              du_cellAt'45'set'45'halted_1344 (coe v0) (coe v1) (coe v2)
                              (coe v21) (coe v23) (coe v5) (coe v6) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_852 v8 v11 v12 v15 v17 v18 v19 v22 v23 v24
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'wf_852
             v8 v11 v12 v15 v17 v18 v19 v22 v23
             (coe
                du_validAtWF'45'set'45'halted_1330 (coe v0) (coe v1) (coe v2)
                (coe v8) (coe v12) (coe v5) (coe v6) (coe v24))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'reg'45'wf_876 v8 v11 v12 v16 v17 v18 v21
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'closure'45'reg'45'wf_876
             v8 v11 v12 v16 v17 v18 v21
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_896 v9 v10 v11 v12 v16 v17 v18 v20
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'ν'45'susp'45'wf_896
             v9 v10 v11 v12 v16 v17
             (coe
                du_cellAt'45'set'45'halted_1344 (coe v0) (coe v1) (coe v2) (coe v9)
                (coe v12) (coe v5) (coe v6) (coe v18))
             v20
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_916 v14 v16 v17 v20 v21 v22
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v25
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'wf_916
                           v14 v16 v17 v20 v21
                           (coe
                              du_validAtWF'45'set'45'halted_1330 (coe v0) (coe v1) (coe v2)
                              (coe v23) (coe v25) (coe v5) (coe v6) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_936 v14 v16 v17 v20 v21 v22
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v23 v24
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v25
                      -> coe
                           MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'wf_936
                           v14 v16 v17 v20 v21
                           (coe
                              du_validAtWF'45'set'45'halted_1330 (coe v0) (coe v1) (coe v2)
                              (coe v24) (coe v25) (coe v5) (coe v6) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'reg'45'wf_954 v15 v17 v19
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inl'45'reg'45'wf_954
             v15 v17 v19
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'reg'45'wf_972 v15 v17 v19
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'inr'45'reg'45'wf_972
             v15 v17 v19
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_988 v13 v15
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v16
               -> coe
                    MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'μ'45'wf_988
                    v13
                    (coe
                       du_validAtWF'45'set'45'halted_1330 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v16) (coe v3))
                       (coe
                          MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.du_eval'7472'_28 v1
                             v3
                             (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v16) (coe v3))
                             (coe MAlonzo.Code.Once.IR.C_out'45'μ_100 v13) v4)
                          (coe (0 :: Integer)))
                       (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_1000 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'int'45'wf_1000
             v13
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_1012 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'float'45'wf_1012
             v13
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_1024 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'str'45'wf_1024
             v13
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_1036 v13
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_valid'45'buffer'45'wf_1036
             v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Machine.ValidAtWFHalted._.cellAt-set-halted
d_cellAt'45'set'45'halted_1344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584
d_cellAt'45'set'45'halted_1344 v0 v1 v2 v3 v4 v5 v6 ~v7 v8
  = du_cellAt'45'set'45'halted_1344 v0 v1 v2 v3 v4 v5 v6 v8
du_cellAt'45'set'45'halted_1344 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_488 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_402 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584 ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_CellAt_584
du_cellAt'45'set'45'halted_1344 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_786 v11 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'ptr_786
             v11 v13 v15
             (coe
                du_validAtWF'45'set'45'halted_1330 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_798 v12
        -> coe
             MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.C_cell'45'inline_798
             v12
      _ -> MAlonzo.RTE.mazUnreachableError
